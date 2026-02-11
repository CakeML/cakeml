(*
  Syntactic properties proofs for wordConvs.
*)
Theory wordConvsProof
Ancestors
  wordLang word_to_word wordConvs word_simp word_alloc word_inst
  word_unreach word_remove word_cse word_elim word_copy
Libs
  preamble

(***
  This theory should serve also as documentation for
  the syntactic properties of wordLang that gets preserved
  across wordLang passes.
  It must NOT depend on the semantics or word_Xproof files.

  word_simp$compile_exp
  ===
    preserves label_rel: extract_labels_compile_exp
    preserves every_inst: compile_exp_no_inst

    preserves subprogs (no export): compile_exp_not_created_subprogs
    preserves code_labels (no export):   word_get_code_labels_word_simp
    preserves good_handlers (no export): word_good_handlers_word_simp

  inst_select
  ===
    preserves label_rel: inst_select_lab_pres (equality on labels)
    creates flat_exp_conventions: inst_select_flat_exp_conventions
    creates full_inst_ok_less (uses every_inst): inst_select_full_inst_ok_less

    preserves subprogs (no export): inst_select_not_created_subprogs
    preserves code_labels (no export):   word_get_code_labels_inst_select
    preserves good_handlers (no export): word_good_handlers_inst_select

  full_ssa_cc_trans
  ===
    preserves label_rel: full_ssa_cc_trans_lab_pres (equality on labels)

    preserves flat_exp_conventions: full_ssa_cc_trans_flat_exp_conventions
    creates wf_cutsets: full_ssa_cc_trans_wf_cutsets

    TODO: move these out of word_allocProof somehow
      preserves full_inst_ok_less: full_ssa_cc_trans_full_inst_ok_less
      creates pre_alloc_conventions: full_ssa_cc_trans_pre_alloc_conventions
      creates distinct_tar_reg: full_ssa_cc_trans_distinct_tar_reg
    TODO ends here

    preserves subprogs (no export): full_ssa_cc_trans_not_created_subprogs
    preserves code_labels (no_export):   word_get_code_labels_full_ssa_cc_trans
    preserves good_handlers (no_export): word_good_handlers_full_ssa_cc_trans

  remove_dead_prog (note this is ran again after remove_unreach)
  ===
    preserves label_rel: remove_dead_prog_conventions (equality on labels)

    preserves flat_exp_conventions: remove_dead_prog_conventions
    preserves full_inst_ok_less: remove_dead_prog_conventions
    preserves pre_alloc_conventions: remove_dead_prog_conventions
    preserves every_inst: remove_dead_prog_conventions
    preserves wf_cutsets: remove_dead_prog_conventions

    preserves subprogs (no export): remove_dead_prog_not_created_subprogs
    preserves code_labels (no export): word_get_code_labels_remove_dead_prog
    preserves good_handlers (no export): word_good_handlers_remove_dead_prog

  word_common_subexp_elim
  ===
    preserves label_rel: extract_labels_word_common_subexp_elim (equality on labels)

    preserves flat_exp_conventions: flat_exp_conventions_word_common_subexp_elim
    preserves wf_cutsets: wf_cutsets_word_common_subexp_elim

    TODO: move these out of word_cseProof somehow
      preserves full_inst_ok_less: full_inst_ok_less_word_common_subexp_elim
      preserves pre_alloc_conventions: pre_alloc_conventions_word_common_subexp_elim
      preserves every_inst_distinct_tar_reg: every_inst_distinct_tar_reg_word_common_subexp_elim
      preserves every_inst_two_reg_inst (unused): word_cse_conventions (unused)
    TODO ends here

    preserves subprogs (no export): word_common_subexp_elim_not_created_subprogs
    preserves code_labels (no export):   word_get_code_labels_word_common_subexp_elim
    preserves good_handlers (no export): word_good_handlers_word_common_subexp_elim

  copy_prop
  ===
    preserves label_rel: extract_labels_copy_prop (equality on labels)

    preserves flat_exp_conventions: flat_exp_conventions_copy_prop
    preserves full_inst_ok_less: full_inst_ok_less_copy_prop
    preserves pre_alloc_conventions: pre_alloc_conventions_copy_prop
    preserves every_inst_distinct_tar_reg: every_inst_distinct_tar_reg_copy_prop
    preserves wf_cutsets: wf_cutsets_copy_prop

    preserves subprogs (no export): copy_prop_not_created_subprogs
    preserves code_labels (no export):   word_get_code_labels_copy_prop
    preserves good_handlers (no export): word_good_handlers_copy_prop

  three_to_two_reg_prog
  ===
    preserves label_rel: three_to_two_reg_prog_lab_pres (equality on labels)

    preserves flat_exp_conventions: three_to_two_reg_prog_flat_exp_conventions
    preserves full_inst_ok_less :three_to_two_reg_prog_full_inst_ok_less:
    preserves pre_alloc_conventions: three_to_two_reg_prog_pre_alloc_conventions
    creates two_reg_inst (from distinct_tar_reg): three_to_two_reg_prog_two_reg_inst
    preserves wf_cutsets: three_to_two_reg_prog_wf_cutsets

    preserves subprogs (no export): three_to_two_reg_prog_not_created_subprogs
    preserves code_labels (no export): word_get_code_labels_three_to_two_reg_prog
    preserves good_handlers (no export): word_good_handlers_three_to_two_reg_prog

  remove_unreach
  ===
    preserves labels_rel: labels_rel_remove_unreach

    preserves flat_exp_conventions: flat_exp_conventions_remove_unreach
    preserves full_inst_ok_less: full_inst_ok_less_remove_unreach
    preserves pre_alloc_conventions: pre_alloc_conventions_remove_unreach
    preserves every_inst: every_inst_remove_unreach
    preserves wf_cutsets: wf_cutsets_remove_unreach

    preserves subprogs (no export): remove_unreach_not_created_subprogs
    preserves code_labels (no export):   word_get_code_labels_remove_unreach
    preserves good_handlers (no export): word_good_handlers_remove_unreach

  word_alloc
  ===
    preserves label_rel: word_alloc_lab_pres (equality on labels)

    preserves flat_exp_conventions: word_alloc_flat_exp_conventions
    preserves two_reg_inst: word_alloc_two_reg_inst

    TODO: move these out of word_allocProof somehow
      preserves full_inst_ok_less: word_alloc_full_inst_ok_less
      creates post_alloc_conventions (from pre_alloc_conventions): pre_post_conventions_word_alloc
    TODO ends here

    preserves subprogs (no export): word_alloc_not_created_subprogs
    preserves code_labels (no export): word_get_code_labels_word_alloc
    preserves good_handlers (no export): word_good_handlers_word_alloc

  remove_must_terminate
  ===
    preserves label_rel: remove_must_terminate_conventions (equality on labels)

    preserves flat_exp_conventions: remove_must_terminate_conventions
    preserves full_inst_ok_less: remove_must_terminate_conventions
    preserves post_alloc_conventions: remove_must_terminate_conventions
    preserves every_inst: remove_must_terminate_conventions

    (subprogs is dealt with separately)
    preserves code_labels (no export): word_get_code_labels_remove_must_terminate
    preserves good_handlers (no export): word_good_handlers_remove_must_terminate

  word_to_word (compile_single and full_compile_single thms)
  ===
    preserves subprogs: compile_single_not_created_subprogs
    preserves good_handlers: word_good_handlers_word_to_word, word_good_handlers_word_to_word_incr
    preserves good_code_labels: word_good_code_labels_word_to_word_incr, word_good_code_labels_word_to_word
***)

(*** word_simp$compile_exp ***)

(* labels_rel *)
Theorem extract_labels_SmartSeq[local]:
   extract_labels (SmartSeq p1 p2) = extract_labels (Seq p1 p2)
Proof
  rw [SmartSeq_def,extract_labels_def]
QED

Theorem extract_labels_Seq_assoc_lemma[local]:
   !p1 p2. extract_labels (Seq_assoc p1 p2) =
            extract_labels p1 ++ extract_labels p2
Proof
  HO_MATCH_MP_TAC Seq_assoc_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_def,extract_labels_def,extract_labels_SmartSeq]
  \\ Cases_on `ret_prog` \\ Cases_on `handler` \\ fs []
  \\ PairCases_on `x` \\ fs []
  \\ PairCases_on `x'` \\ fs []
QED

Theorem extract_labels_Seq_assoc[local]:
   extract_labels (Seq_assoc Skip p) = extract_labels p
Proof
  fs [extract_labels_Seq_assoc_lemma,extract_labels_def]
QED

Theorem extract_labels_drop_consts_1[local]:
  extract_labels (drop_consts cs ls) = []
Proof
  Induct_on`ls`>>rw[drop_consts_def]>>
  every_case_tac>>
  rw[extract_labels_SmartSeq,extract_labels_def]
QED

Theorem extract_labels_drop_consts[local,simp]:
  extract_labels (SmartSeq (drop_consts cs ls) p) = extract_labels p
Proof
  rw[extract_labels_SmartSeq,extract_labels_def,extract_labels_drop_consts_1]
QED

Theorem extract_labels_const_fp_loop[local]:
  !p cs p1 cs1.
  const_fp_loop p cs = (p1,cs1) ==>
  labels_rel (extract_labels p) (extract_labels p1)
Proof
  ho_match_mp_tac const_fp_loop_ind
  \\ ntac 6 (conj_tac THEN1
   (fs [const_fp_loop_def] \\ rw [] \\ fs [extract_labels_def]
    \\ every_case_tac
    \\ fs [const_fp_loop_def] \\ rw [] \\ fs [extract_labels_def]
    \\ pairarg_tac \\ fs [] \\ rw [] \\ fs [extract_labels_def]
    \\ pairarg_tac \\ fs [] \\ rw [] \\ fs [extract_labels_def]
    \\ match_mp_tac labels_rel_APPEND \\ fs []))
  \\ reverse (rpt conj_tac)
  \\ TRY (fs [const_fp_loop_def] \\ rw [] \\ fs [extract_labels_def] \\ NO_TAC)
  THEN1 (* Call *)
   (rw [] \\ fs [const_fp_loop_def]
    \\ gvs[AllCaseEqs()]
    \\ pairarg_tac \\ fs [] \\ rw []
    \\ fs [extract_labels_def]
    \\ once_rewrite_tac [CONS_APPEND]
    \\ match_mp_tac labels_rel_APPEND \\ fs [])
  \\ (* If *) rw [] \\ fs [const_fp_loop_def]
  \\ every_case_tac \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rw []
  \\ fs [extract_labels_def]
  \\ TRY (match_mp_tac labels_rel_APPEND \\ fs [])
  \\ fs [labels_rel_def,ALL_DISTINCT_APPEND,SUBSET_DEF]
QED

Theorem extract_labels_const_fp[local]:
   labels_rel (extract_labels p) (extract_labels (const_fp p))
Proof
  fs [const_fp_def] \\ Cases_on `const_fp_loop p LN`
  \\ drule extract_labels_const_fp_loop
  \\ simp []
QED

Theorem labels_rel_append_imp[local]:
  labels_rel (Y ++ X) Z ==> labels_rel (X ++ Y) Z
Proof
  metis_tac [PERM_APPEND, labels_rel_TRANS, PERM_IMP_labels_rel]
QED

fun FIRST_THEN tacs tac = FIRST (map (fn t => t \\ tac) tacs)

val try_cancel_labels_rel_append =
  FIRST_THEN [ALL_TAC, irule labels_rel_append_imp]
  (FIRST_THEN [REWRITE_TAC [GSYM APPEND_ASSOC],
      REWRITE_TAC [APPEND_ASSOC], ONCE_REWRITE_TAC [APPEND_ASSOC]]
  (FIRST_THEN [ALL_TAC, irule labels_rel_append_imp]
  (FIRST_THEN [REWRITE_TAC [GSYM APPEND_ASSOC], REWRITE_TAC [APPEND_ASSOC]]
  (drule_at_then Any irule labels_rel_APPEND))));

Theorem const_fp_loop_Seq[local] =
  const_fp_loop_def |> BODY_CONJUNCTS
  |> filter (can (find_term (fn t => total (fst o dest_const) t = SOME "Seq")) o concl)
  |> LIST_CONJ

(* The tricky part: to prove this syntactic property (and only for this) we
   have to show that the strategy actually works, and that any program which
   the hoist mechanism hoists will simplify (via const_fp) back to a program
   in which nothing is duplicated. *)
Theorem const_fp_loop_dummy_cases[local]:
  const_fp_loop (If cmp lhs rhs (Raise 1) (Raise 2)) cs = (p2, cs2) ==>
  (dest_Raise_num p2 = 1 /\
  (! br1 br2 . const_fp_loop (If cmp lhs rhs br1 br2) cs = const_fp_loop br1 cs)) \/
  (dest_Raise_num p2 = 2 /\
  (! br1 br2 . const_fp_loop (If cmp lhs rhs br1 br2) cs = const_fp_loop br2 cs)) \/
  (dest_Raise_num p2 = 0)
Proof
  rw [const_fp_loop_def, dest_Raise_num_def]
  \\ gvs [CaseEq "option", CaseEq "bool"]
QED

Theorem dest_If_thm[local]:
   dest_If x2 = SOME (g1,g2,g3,g4,g5) <=> x2 = If g1 g2 g3 g4 g5
Proof
  Cases_on `x2` \\ fs [dest_If_def]
QED

Theorem labels_rel_hoist2[local]:
  ! N p1 interm dummy p2 s.
  try_if_hoist2 N p1 interm dummy p2 = SOME p3 ==>
  dest_If p2 = SOME (cmp, lhs, rhs, br1, br2) ==>
  dummy = If cmp lhs rhs (Raise 1) (Raise 2) ==>
  extract_labels interm = [] ==>
  labels_rel (extract_labels p1 ++ extract_labels p2)
    (extract_labels p3)
Proof
  ho_match_mp_tac try_if_hoist2_ind
  \\ rpt gen_tac
  \\ rpt disch_tac
  \\ REWRITE_TAC [Once try_if_hoist2_def]
  \\ rw []
  \\ fs [CaseEq "bool", CaseEq "wordLang$prog",
        CaseEq "option", CaseEq "prod"]
  \\ gvs []
  \\ fs [extract_labels_def, dest_If_thm]
  >- (
    fs [is_simple_def] \\ every_case_tac
    \\ gs [extract_labels_def]
  )
  >- (
    fs [const_fp_def, const_fp_loop_Seq]
    \\ rpt (pairarg_tac \\ fs [])
    \\ gvs [dest_Seq_def]
    \\ simp [Once const_fp_loop_def]
    \\ rpt (dxrule const_fp_loop_dummy_cases)
    \\ rw [] \\ fs []
    \\ gs []
    \\ fs [const_fp_loop_Seq]
    \\ rpt (pairarg_tac \\ fs [])
    \\ gvs [extract_labels_def]
    \\ imp_res_tac extract_labels_const_fp_loop
    \\ gs [extract_labels_def, EVAL ``labels_rel [] _``]
    \\ rpt try_cancel_labels_rel_append
    \\ simp []
  )
  >- (
    fs [const_fp_def, const_fp_loop_Seq]
    \\ rpt (pairarg_tac \\ fs [])
    \\ gvs [dest_Seq_def]
    \\ simp [Once const_fp_loop_def]
    \\ rpt (dxrule const_fp_loop_dummy_cases)
    \\ rw [] \\ fs []
    \\ gs []
    \\ fs [const_fp_loop_Seq]
    \\ rpt (pairarg_tac \\ fs [])
    \\ gvs [extract_labels_def]
    \\ imp_res_tac extract_labels_const_fp_loop
    \\ gs [extract_labels_def, EVAL ``labels_rel [] _``]
    \\ rpt try_cancel_labels_rel_append
    \\ simp []
  )
QED

Theorem labels_rel_simp_duplicate_if[local]:
  !p. labels_rel (extract_labels p) (extract_labels (simp_duplicate_if p))
Proof
  ho_match_mp_tac simp_duplicate_if_ind
  \\ rw []
  \\ simp [Once simp_duplicate_if_def]
  \\ Cases_on `p` \\ fs []
  \\ simp [extract_labels_def]
  \\ every_case_tac
  \\ fs [extract_labels_def, labels_rel_CONS, labels_rel_APPEND]
  \\ simp [extract_labels_Seq_assoc_lemma, extract_labels_def]
  \\ fs [try_if_hoist1_def, CaseEq "option", CaseEq "prod", EXISTS_PROD]
  \\ drule labels_rel_hoist2
  \\ rw [extract_labels_def]
  \\ drule_at_then Any irule labels_rel_TRANS
  \\ irule labels_rel_APPEND
  \\ simp []
QED

Theorem labels_rel_push_out_if[local]:
  !p. labels_rel (extract_labels p) (extract_labels (push_out_if p))
Proof
  simp[push_out_if_def]
  \\ ho_match_mp_tac push_out_if_aux_ind
  \\ rw[]
  \\ simp_tac(srw_ss())[Once push_out_if_aux_def]
  \\ simp $ map (Q.ISPEC `FST:'free_tyvar # 'free_tyvar2 -> 'free_tyvar` o TypeBase.case_rand_of) $
     [``:'a prog``, ``:'a # 'b``,``:'a option``,``:bool``]
  \\ rpt (PURE_TOP_CASE_TAC \\ simp_tac(srw_ss())[])
  \\ fs[] \\ simp[extract_labels_def]
  \\ metis_tac[ labels_rel_refl,labels_rel_APPEND,labels_rel_append_imp]
QED

Theorem extract_labels_compile_exp:
  !p. labels_rel (extract_labels p)
                 (extract_labels (word_simp$compile_exp p))
Proof
  rw [word_simpTheory.compile_exp_def] >>
  irule labels_rel_TRANS >> ONCE_REWRITE_TAC [CONJ_COMM] >>
  irule_at Any labels_rel_push_out_if >>
  irule labels_rel_TRANS >> ONCE_REWRITE_TAC [CONJ_COMM] >>
  irule_at Any labels_rel_simp_duplicate_if >>
  irule labels_rel_TRANS >> ONCE_REWRITE_TAC [CONJ_COMM] >>
  irule_at Any extract_labels_const_fp >>
  irule labels_rel_TRANS >> ONCE_REWRITE_TAC [CONJ_COMM] >>
  simp [extract_labels_Seq_assoc] >>
  metis_tac[ labels_rel_refl]
QED

(* inst_ok_less *)
Theorem dest_Seq_no_inst[local]:
  ∀prog.
  every_inst P prog ⇒
  every_inst P (FST (dest_Seq prog)) ∧
  every_inst P (SND (dest_Seq prog))
Proof
  ho_match_mp_tac dest_Seq_ind>>rw[dest_Seq_def]>>fs[every_inst_def]
QED

Theorem Seq_assoc_no_inst[local]:
  ∀p1 p2.
  every_inst P p1 ∧ every_inst P p2 ⇒
  every_inst P (Seq_assoc p1 p2)
Proof
  ho_match_mp_tac Seq_assoc_ind>>
  fs[Seq_assoc_def,SmartSeq_def]>>rw[]>>
  fs[every_inst_def]>>
  every_case_tac>>fs[]
QED

Theorem every_inst_SmartSeq[local]:
  every_inst P (SmartSeq p q) =
  (every_inst P p ∧ every_inst P q)
Proof
  rw[SmartSeq_def,every_inst_def]
QED

Theorem every_inst_drop_consts[local,simp]:
  every_inst P (SmartSeq (drop_consts cs ls) p) =
  every_inst P p
Proof
  rw[every_inst_SmartSeq]>>
  `every_inst P (drop_consts cs ls)` by (
    Induct_on`ls`>>rw[drop_consts_def]>>every_case_tac>>
    rw[every_inst_def,every_inst_SmartSeq] )>>
  rw[]
QED

Theorem every_inst_const_fp[local]:
   ∀prog.
    every_inst P prog ⇒
    every_inst P (const_fp prog)
Proof
  strip_tac
  \\ fs [const_fp_def] \\ Cases_on `const_fp_loop prog LN`
  \\ rename1 `const_fp_loop p cs = (p1,cs1)` \\ fs []
  \\ pop_assum mp_tac
  \\ qspec_tac (`cs1`,`cs1`) \\ qspec_tac (`p1`,`p1`)
  \\ qspec_tac (`cs`,`cs`) \\ qspec_tac (`p`,`p`)
  \\ ho_match_mp_tac const_fp_loop_ind \\ rw []
  \\ fs [const_fp_loop_def] \\ rw [] \\ fs [every_inst_def]
  \\ every_case_tac \\ rw [] \\ fs [every_inst_def]
  \\ pairarg_tac \\ fs [] \\ rw [] \\ fs [every_inst_def]
  \\ pairarg_tac \\ fs [] \\ rw [] \\ fs [every_inst_def]
QED

Theorem try_if_hoist2_no_inst[local]:
  ! N p1 interm dummy p2 s.
  try_if_hoist2 N p1 interm dummy p2 = SOME p3 ==>
  every_inst P p1 ==>
  every_inst P interm ==>
  every_inst P p2 ==>
  every_inst P p3
Proof
  ho_match_mp_tac try_if_hoist2_ind
  \\ rpt gen_tac
  \\ rpt disch_tac
  \\ REWRITE_TAC [Once try_if_hoist2_def]
  \\ rw []
  \\ fs [CaseEq "bool", CaseEq "wordLang$prog",
        CaseEq "option", CaseEq "prod"]
  \\ gvs [dest_If_thm]
  \\ fs [every_inst_def, every_inst_const_fp]
QED

Theorem simp_duplicate_if_no_inst[local]:
  !p. every_inst P p ==> every_inst P (simp_duplicate_if p)
Proof
  ho_match_mp_tac simp_duplicate_if_ind
  \\ rw []
  \\ simp [Once simp_duplicate_if_def]
  \\ Cases_on `p` \\ fs []
  \\ fs [every_inst_def]
  \\ every_case_tac \\ fs []
  \\ fs [every_inst_def]
  \\ fs [try_if_hoist1_def, CaseEq "option", CaseEq "prod"]
  \\ imp_res_tac try_if_hoist2_no_inst
  \\ gs [dest_If_thm]
  \\ fs [every_inst_def, Seq_assoc_no_inst, every_inst_const_fp]
QED

Theorem simp_push_out_if_no_inst[local]:
  !p. every_inst P p ==> every_inst P (push_out_if p)
Proof
  simp [push_out_if_def]
  \\ ho_match_mp_tac push_out_if_aux_ind
  \\ rw []
  \\ simp_tac(srw_ss())[Once push_out_if_aux_def]
  \\ simp $ map (Q.ISPEC `FST:'free_tyvar # 'free_tyvar2 -> 'free_tyvar` o TypeBase.case_rand_of) $
     [``:'a prog``, ``:'a # 'b``,``:'a option``,``:bool``]
  \\ rpt (PURE_TOP_CASE_TAC \\ asm_simp_tac(srw_ss())[])
  \\ fs[every_inst_def]
QED

Theorem compile_exp_no_inst:
  ∀prog.
    every_inst P prog ⇒
    every_inst P (compile_exp prog)
Proof
  rw[compile_exp_def]>>
  rpt (MAP_FIRST irule [Seq_assoc_no_inst,every_inst_def,
            every_inst_const_fp,simp_duplicate_if_no_inst,
            simp_push_out_if_no_inst]) >>
  simp[every_inst_def]
QED

Theorem not_created_subprogs_SmartSeq[local]:
   not_created_subprogs P (SmartSeq p1 p2) =
   (not_created_subprogs P p1 /\ not_created_subprogs P p2)
Proof
  rw [SmartSeq_def,not_created_subprogs_def]
QED

Theorem not_created_subprogs_Seq_assoc[local]:
  !p1 p2. not_created_subprogs P (Seq_assoc p1 p2) =
  (not_created_subprogs P p1 /\ not_created_subprogs P p2)
Proof
  ho_match_mp_tac Seq_assoc_ind
  \\ fs [Seq_assoc_def, not_created_subprogs_def, not_created_subprogs_SmartSeq]
  \\ rw []
  \\ every_case_tac
  \\ EQ_TAC \\ rw []
  \\ fs [UNION_ASSOC]
QED

Theorem not_created_subprogs_drop_consts[local,simp]:
  not_created_subprogs P (SmartSeq (drop_consts cs ls) p) =
  not_created_subprogs P p
Proof
  rw[not_created_subprogs_SmartSeq]>>
  `not_created_subprogs P (drop_consts cs ls)` by (
    Induct_on`ls`>>rw[drop_consts_def]>>every_case_tac>>
    rw[not_created_subprogs_def,not_created_subprogs_SmartSeq])>>
  rw[]
QED

Theorem not_created_subprogs_const_fp_loop[local]:
  !p cs p1 cs1.
  const_fp_loop p cs = (p1,cs1) ==>
  not_created_subprogs P p ==>
  not_created_subprogs P p1
Proof
  ho_match_mp_tac const_fp_loop_ind
  \\ rw []
  \\ gvs [not_created_subprogs_def, const_fp_loop_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ gvs [CaseEq "exp", CaseEq "option", CaseEq "bool", CaseEq "prod", not_created_subprogs_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ gvs [not_created_subprogs_def]
QED

Theorem not_created_subprogs_const_fp[local]:
  not_created_subprogs P p ==>
  not_created_subprogs P (const_fp p)
Proof
  rw [const_fp_def]
  \\ Cases_on `const_fp_loop p LN` \\ fs []
  \\ imp_res_tac not_created_subprogs_const_fp_loop
QED

Theorem not_created_subprogs_hoist2[local]:
  ! N p1 interm dummy p2.
  try_if_hoist2 N p1 interm dummy p2 = SOME p3 ==>
  not_created_subprogs P p1 ==> not_created_subprogs P interm ==>
  not_created_subprogs P p2 ==>
  not_created_subprogs P p3
Proof
  ho_match_mp_tac try_if_hoist2_ind
  \\ rpt gen_tac
  \\ disch_tac
  \\ REWRITE_TAC [Once try_if_hoist2_def]
  \\ rw []
  \\ fs [CaseEq "bool", CaseEq "wordLang$prog",
        CaseEq "option", CaseEq "prod"]
  \\ gvs []
  \\ gs [not_created_subprogs_def, dest_If_thm]
  \\ irule not_created_subprogs_const_fp
  \\ fs [not_created_subprogs_def]
QED

Theorem not_created_subprogs_simp_duplicate_if[local]:
  !p. not_created_subprogs P p ==>
  not_created_subprogs P (simp_duplicate_if p)
Proof
  ho_match_mp_tac simp_duplicate_if_ind
  \\ rw []
  \\ simp [Once simp_duplicate_if_def]
  \\ Cases_on `p` \\ fs [not_created_subprogs_def]
  \\ every_case_tac \\ fs []
  \\ simp [not_created_subprogs_Seq_assoc, not_created_subprogs_def]
  \\ fs [try_if_hoist1_def, CaseEq "option", CaseEq "prod", EXISTS_PROD]
  \\ drule_then drule not_created_subprogs_hoist2
  \\ fs [not_created_subprogs_def]
QED

Theorem not_created_subprogs_push_out_if[local]:
  !p.
  not_created_subprogs P (push_out_if p) =
  not_created_subprogs P p
Proof
  simp [push_out_if_def]
  \\ ho_match_mp_tac push_out_if_aux_ind
  \\ rw []
  \\ simp_tac(srw_ss())[Once push_out_if_aux_def]
  \\ simp $ map (Q.ISPEC `FST:'free_tyvar # 'free_tyvar2 -> 'free_tyvar` o TypeBase.case_rand_of) $
     [``:'a prog``, ``:'a # 'b``,``:'a option``,``:bool``]
  \\ rpt (PURE_TOP_CASE_TAC \\ asm_simp_tac(srw_ss())[])
  \\ fs[not_created_subprogs_def,EQ_IMP_THM]
QED

Theorem compile_exp_not_created_subprogs[local]:
  not_created_subprogs P p ==>
  not_created_subprogs P (compile_exp p)
Proof
  rw [compile_exp_def, not_created_subprogs_const_fp,not_created_subprogs_push_out_if,
    not_created_subprogs_simp_duplicate_if, not_created_subprogs_Seq_assoc,
    not_created_subprogs_def]
QED

Theorem word_get_code_labels_SmartSeq[local,simp]:
  word_get_code_labels (SmartSeq p q) =
  word_get_code_labels p ∪ word_get_code_labels q
Proof
  rw[SmartSeq_def]
QED

Theorem word_get_code_labels_drop_consts[local,simp]:
  ∀args.
  word_get_code_labels (drop_consts l args) = {}
Proof
  Induct>>rw[drop_consts_def]>>
  every_case_tac>>simp[]
QED

Theorem word_get_code_labels_const_fp_loop[local]:
  ∀p l.
  word_get_code_labels (FST (const_fp_loop p l)) ⊆ word_get_code_labels p
Proof
  ho_match_mp_tac const_fp_loop_ind \\ rw []
  \\ fs [const_fp_loop_def]
  \\ every_case_tac\\ fs[]
  \\ rpt (pairarg_tac \\ fs[])
  \\ fs[SUBSET_DEF] \\ metis_tac[]
QED

Theorem word_good_handlers_SmartSeq[local,simp]:
  word_good_handlers n (SmartSeq p q) ⇔
  word_good_handlers n p ∧
  word_good_handlers n q
Proof
  rw[SmartSeq_def]
QED

Theorem word_good_handlers_drop_consts[local,simp]:
  ∀args.
  word_good_handlers n (drop_consts l args)
Proof
  Induct>>rw[drop_consts_def]>>
  every_case_tac>>simp[]
QED

Theorem word_good_handlers_const_fp_loop[local]:
  ∀p l.
  word_good_handlers n p ⇒
  word_good_handlers n (FST (const_fp_loop p l))
Proof
  ho_match_mp_tac const_fp_loop_ind \\ rw []
  \\ fs [const_fp_loop_def]
  \\ every_case_tac\\ fs[]
  \\ rpt (pairarg_tac \\ fs[])
QED

Theorem word_get_code_labels_Seq_assoc[local]:
  ∀p1 p2.
  word_get_code_labels (Seq_assoc p1 p2) = word_get_code_labels p1 ∪ word_get_code_labels p2
Proof
  ho_match_mp_tac Seq_assoc_ind>>rw[]>>
  fs[Seq_assoc_def,SmartSeq_def]>>rw[]>>
  fs[UNION_ASSOC]>>
  every_case_tac>>fs[]
QED

Theorem word_good_handlers_Seq_assoc[local]:
  ∀p1 p2.
  word_good_handlers n (Seq_assoc p1 p2) ⇔
  word_good_handlers n p1 ∧ word_good_handlers n p2
Proof
  ho_match_mp_tac Seq_assoc_ind>>rw[]>>
  fs[Seq_assoc_def,SmartSeq_def]>>rw[]>>
  every_case_tac>>fs[]>>metis_tac[]
QED

Theorem word_good_handlers_try_if_hoist2[local]:
  ! N p1 interm dummy p2 s.
  try_if_hoist2 N p1 interm dummy p2 = SOME p3 ==>
  word_good_handlers n p1 /\ word_good_handlers n p2 /\ word_good_handlers n interm ==>
  word_good_handlers n p3
Proof
  ho_match_mp_tac try_if_hoist2_ind
  \\ rpt gen_tac
  \\ rpt disch_tac
  \\ REWRITE_TAC [Once try_if_hoist2_def]
  \\ rpt disch_tac
  \\ fs [CaseEq "bool", CaseEq "wordLang$prog",
        CaseEq "option", CaseEq "prod"]
  \\ gvs []
  \\ gs [dest_If_thm]
  \\ simp [const_fp_def]
  \\ irule word_good_handlers_const_fp_loop
  \\ simp []
QED

Theorem word_good_handlers_simp_duplicate_if[local]:
  !p. word_good_handlers n p ==> word_good_handlers n (simp_duplicate_if p)
Proof
  ho_match_mp_tac simp_duplicate_if_ind
  \\ rw []
  \\ simp [Once simp_duplicate_if_def]
  \\ Cases_on `p` \\ fs []
  \\ simp []
  \\ every_case_tac
  \\ fs []
  \\ fs [try_if_hoist1_def, CaseEq "option", CaseEq "prod", EXISTS_PROD]
  \\ drule word_good_handlers_try_if_hoist2
  \\ fs [word_good_handlers_Seq_assoc]
QED

Theorem word_good_handlers_simp_push_out_if[local]:
  !p. word_good_handlers n p ==> word_good_handlers n (push_out_if p)
Proof
  simp [push_out_if_def]
  \\ ho_match_mp_tac push_out_if_aux_ind
  \\ rw []
  \\ simp_tac(srw_ss())[Once push_out_if_aux_def]
  \\ simp $ map (Q.ISPEC `FST:'free_tyvar # 'free_tyvar2 -> 'free_tyvar` o TypeBase.case_rand_of) $
     [``:'a prog``, ``:'a # 'b``,``:'a option``,``:bool``]
  \\ rpt (PURE_TOP_CASE_TAC \\ asm_simp_tac(srw_ss())[])
  \\ fs[]
QED

Theorem word_good_handlers_word_simp[local]:
  ∀ps.
  word_good_handlers n ps ⇒
  word_good_handlers n (word_simp$compile_exp ps)
Proof
  rw[compile_exp_def]>>
  irule word_good_handlers_simp_push_out_if >>
  irule word_good_handlers_simp_duplicate_if >>
  simp [const_fp_def] >>
  match_mp_tac word_good_handlers_const_fp_loop>>
  fs[word_good_handlers_Seq_assoc]
QED

Theorem word_get_code_labels_try_if_hoist2[local]:
  ! N p1 interm dummy p2 s.
  try_if_hoist2 N p1 interm dummy p2 = SOME p3 ==>
  word_get_code_labels p3 SUBSET
  (word_get_code_labels p1 UNION word_get_code_labels interm UNION word_get_code_labels p2)
Proof
  ho_match_mp_tac try_if_hoist2_ind
  \\ rpt gen_tac
  \\ rpt disch_tac
  \\ REWRITE_TAC [Once try_if_hoist2_def]
  \\ rpt disch_tac
  \\ fs [CaseEq "bool", CaseEq "wordLang$prog",
        CaseEq "option", CaseEq "prod"]
  \\ gvs []
  \\ gs [dest_If_thm]
  >- (
    drule_then irule SUBSET_TRANS
    \\ simp [SUBSET_DEF]
  )
  >- (
    irule_at (Pat `word_get_code_labels (const_fp _) SUBSET _`) SUBSET_TRANS
    \\ simp [const_fp_def]
    \\ irule_at Any word_get_code_labels_const_fp_loop
    \\ simp [SUBSET_DEF, DISJ_IMP_THM]
  )
  >- (
    irule_at (Pat `word_get_code_labels (const_fp _) SUBSET _`) SUBSET_TRANS
    \\ simp [const_fp_def]
    \\ irule_at Any word_get_code_labels_const_fp_loop
    \\ simp [SUBSET_DEF, DISJ_IMP_THM]
  )
QED

Theorem word_get_code_labels_simp_duplicate_if[local]:
  !p. word_get_code_labels (simp_duplicate_if p) SUBSET word_get_code_labels p
Proof
  ho_match_mp_tac simp_duplicate_if_ind
  \\ rw []
  \\ simp [Once simp_duplicate_if_def]
  \\ Cases_on `p` \\ fs []
  \\ simp []
  \\ every_case_tac
  \\ fs []
  \\ fs [SUBSET_DEF]
  \\ fs [try_if_hoist1_def, CaseEq "option", CaseEq "prod", EXISTS_PROD]
  \\ drule word_get_code_labels_try_if_hoist2
  \\ fs [word_get_code_labels_Seq_assoc, SUBSET_DEF]
  \\ metis_tac []
QED

Theorem word_get_code_labels_push_out_if[local]:
  !p. word_get_code_labels (push_out_if p) SUBSET word_get_code_labels p
Proof
  simp [push_out_if_def]
  \\ ho_match_mp_tac push_out_if_aux_ind
  \\ rw []
  \\ simp_tac(srw_ss())[Once push_out_if_aux_def]
  \\ simp $ map (Q.ISPEC `FST:'free_tyvar # 'free_tyvar2 -> 'free_tyvar` o TypeBase.case_rand_of) $
     [``:'a prog``, ``:'a # 'b``,``:'a option``,``:bool``]
  \\ rpt (PURE_TOP_CASE_TAC \\ asm_simp_tac(srw_ss())[])
  \\ fs[] \\ ASM_SET_TAC[]
QED

Theorem word_get_code_labels_word_simp[local]:
  ∀ps.
  word_get_code_labels (word_simp$compile_exp ps) ⊆
  word_get_code_labels ps
Proof
  rw [compile_exp_def]>>
  irule SUBSET_TRANS >> irule_at Any word_get_code_labels_push_out_if >>
  irule SUBSET_TRANS >> irule_at Any word_get_code_labels_simp_duplicate_if >>
  simp [const_fp_def] >>
  irule SUBSET_TRANS >> irule_at Any word_get_code_labels_const_fp_loop >>
  simp [word_get_code_labels_Seq_assoc]
QED


(*** inst_select ***)

(* label preservation stuff *)
Theorem inst_select_exp_no_lab[local]:
  ∀c temp temp' exp.
  extract_labels (inst_select_exp c temp temp' exp) = []
Proof
  ho_match_mp_tac inst_select_exp_ind>>
  rw[inst_select_exp_def]>>fs[extract_labels_def]>>
  rpt(TOP_CASE_TAC>>fs[extract_labels_def,inst_select_exp_def])
QED

Theorem inst_select_lab_pres:
  ∀c temp prog.
    extract_labels prog = extract_labels (inst_select c temp prog)
Proof
  ho_match_mp_tac inst_select_ind>>rw[inst_select_def,extract_labels_def]>>
  TRY(metis_tac[inst_select_exp_no_lab])>>
  EVERY_CASE_TAC>>fs[extract_labels_def]>>
  TRY(metis_tac[inst_select_exp_no_lab])
QED

(* inst_select syntax *)
Theorem inst_select_exp_flat_exp_conventions[local]:
  ∀c tar temp exp.
  flat_exp_conventions (inst_select_exp c tar temp exp)
Proof
  ho_match_mp_tac inst_select_exp_ind>>srw_tac[][]>>full_simp_tac(srw_ss())[inst_select_exp_def,flat_exp_conventions_def,LET_THM]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[flat_exp_conventions_def,inst_select_exp_def,LET_THM]
QED

Theorem inst_select_flat_exp_conventions:
  ∀c temp prog.
    flat_exp_conventions (inst_select c temp prog)
Proof
  ho_match_mp_tac inst_select_ind >>srw_tac[][]>>
  full_simp_tac(srw_ss())[flat_exp_conventions_def,inst_select_def,LET_THM]>>
  EVERY_CASE_TAC>>
  full_simp_tac(srw_ss())[flat_exp_conventions_def]>>
  metis_tac[inst_select_exp_flat_exp_conventions]
QED

Theorem inst_select_exp_not_created_subprogs[local]:
  not_created_subprogs P (inst_select_exp c c' n exp)
Proof
  MAP_EVERY qid_spec_tac [‘exp’, ‘n’, ‘c'’, ‘c’]>>
  ho_match_mp_tac word_instTheory.inst_select_exp_ind>>
  rw[word_instTheory.inst_select_exp_def, not_created_subprogs_def]>>
  every_case_tac>>
  gs[not_created_subprogs_def, word_instTheory.inst_select_exp_def]
QED

Theorem inst_select_not_created_subprogs[local]:
  not_created_subprogs P prog ⇒
  not_created_subprogs P (inst_select c n prog)
Proof
  MAP_EVERY qid_spec_tac [‘prog’, ‘n’, ‘c’]>>
  ho_match_mp_tac word_instTheory.inst_select_ind>>
  rw[not_created_subprogs_def]>>
  every_case_tac>>
  gs[inst_select_exp_not_created_subprogs, word_instTheory.inst_select_def,
     not_created_subprogs_def]>>
  every_case_tac>>
  gs[inst_select_exp_not_created_subprogs, word_instTheory.inst_select_def,
     not_created_subprogs_def]
QED

(*Less restrictive version of inst_ok guaranteed by inst_select*)
Theorem inst_select_exp_full_inst_ok_less[local]:
  ∀c tar temp exp.
  addr_offset_ok c 0w ⇒
  full_inst_ok_less c (inst_select_exp c tar temp exp)
Proof
  ho_match_mp_tac inst_select_exp_ind>>rw[]>>
  fs[inst_select_exp_def,LET_THM,inst_ok_less_def,full_inst_ok_less_def]>>
  every_case_tac>>fs[full_inst_ok_less_def,inst_ok_less_def,inst_select_exp_def,LET_THM]
QED

Theorem inst_select_full_inst_ok_less:
  ∀c temp prog.
    addr_offset_ok c 0w ∧
    hw_offset_ok c 0w ∧
    byte_offset_ok c 0w ∧
    every_inst (inst_ok_less c) prog
    ⇒
    full_inst_ok_less c (inst_select c temp prog)
Proof
  ho_match_mp_tac inst_select_ind >>
  rw[inst_select_def,full_inst_ok_less_def,every_inst_def] >>
  EVERY_CASE_TAC >>
  fs[inst_select_def,full_inst_ok_less_def,inst_ok_less_def,every_inst_def,exp_to_addr_def]>>
  metis_tac[inst_select_exp_full_inst_ok_less]
QED

Theorem word_get_code_labels_inst_select_exp[local]:
  ∀a b c exp.
  word_get_code_labels (inst_select_exp a b c exp) = {}
Proof
  ho_match_mp_tac inst_select_exp_ind>>rw[]>>
  fs[inst_select_exp_def]>>
  every_case_tac>>fs[inst_select_exp_def]
QED

Theorem word_get_code_labels_inst_select[local]:
  ∀ac v ps.
  word_get_code_labels (inst_select ac v ps) =
  word_get_code_labels ps
Proof
  ho_match_mp_tac inst_select_ind>>rw[]>>
  fs[inst_select_def]>>
  every_case_tac>>fs[word_get_code_labels_inst_select_exp]
QED

Theorem word_good_handlers_inst_select_exp[local]:
  ∀a b c exp.
  word_good_handlers n (inst_select_exp a b c exp)
Proof
  ho_match_mp_tac inst_select_exp_ind>>rw[]>>
  fs[inst_select_exp_def]>>
  every_case_tac>>fs[inst_select_exp_def]
QED

Theorem word_good_handlers_inst_select[local]:
  ∀ac v ps.
  word_good_handlers n (inst_select ac v ps) ⇔
  word_good_handlers n ps
Proof
  ho_match_mp_tac inst_select_ind>>rw[]>>
  fs[inst_select_def]>>
  every_case_tac>>fs[word_good_handlers_inst_select_exp]
QED

(*** full_ssa_cc_trans ***)
Theorem fake_moves_no_labs[local]:
  ∀ls a b c d e f g h.
  fake_moves prio ls a b c = (d,e,f,g,h) ⇒
  extract_labels d = [] ∧ extract_labels e = []
Proof
  Induct>>
  fs[fake_moves_def,extract_labels_def,fake_move_def]>>rw[]>>
  rpt(pairarg_tac>>fs[])>>
  EVERY_CASE_TAC>>fs[]>>rveq>>fs[extract_labels_def]>>
  metis_tac[]
QED

Theorem full_ssa_cc_trans_lab_pres:
  ∀prog n.
  extract_labels prog =
  extract_labels (full_ssa_cc_trans n prog)
Proof
  rw[full_ssa_cc_trans_def,setup_ssa_def,list_next_var_rename_move_def]>>
  ntac 3 (pairarg_tac>>fs[])>>rveq>>fs[extract_labels_def]>>
  pop_assum kall_tac >> pop_assum mp_tac>>
  map_every qid_spec_tac (rev[`prog`,`ssa`,`n'`,`prog'`,`ssa'`,`na'`])>>
  ho_match_mp_tac ssa_cc_trans_ind>>rw[extract_labels_def,ssa_cc_trans_def,list_next_var_rename_move_def,fix_inconsistencies_def]>>
  rveq>>fs[extract_labels_def]>>EVERY_CASE_TAC>>
  rpt(pairarg_tac>>fs[]>>rveq>>fs[extract_labels_def])
  >-
    (Cases_on`i`>>TRY(Cases_on`a`)>>TRY(Cases_on`m`)>>TRY(Cases_on`r`)>>
    TRY(Cases_on`f`)>>
    fs[ssa_cc_trans_inst_def,next_var_rename_def]>>
    every_case_tac>>rw[]>>
    fs[extract_labels_def])
  >>
  imp_res_tac fake_moves_no_labs>>
  fs[]
QED

Theorem ssa_cc_trans_inst_not_created_subprogs[local]:
  ssa_cc_trans_inst i ssa na = (i',ssa',na') ⇒
  not_created_subprogs P i'
Proof
  MAP_EVERY qid_spec_tac [‘i'’, ‘ssa'’, ‘na'’, ‘na’, ‘ssa’, ‘i’]>>
  recInduct word_allocTheory.ssa_cc_trans_inst_ind>>
  rw[word_allocTheory.ssa_cc_trans_inst_def,
     not_created_subprogs_def]>>
  rpt (pairarg_tac>>gs[])>>
  rw[word_allocTheory.ssa_cc_trans_inst_def,
     not_created_subprogs_def]>>
  every_case_tac>>rw[]>>rveq>>
  gs[word_allocTheory.next_var_rename_def,
     not_created_subprogs_def]
QED

Theorem fake_moves_not_created_subprogs[local]:
  fake_moves prio ls nL nR n = (prog1, prog2, n' ,ssa, ssa') ⇒
  not_created_subprogs P prog1 ∧ not_created_subprogs P prog2
Proof
  MAP_EVERY qid_spec_tac [‘ssa'’, ‘ssa’, ‘n'’, ‘prog2’, ‘prog1’, ‘n’, ‘nR’, ‘NL’, ‘ls’]>>
  Induct_on ‘ls’>>
  gs[word_allocTheory.fake_moves_def,
     not_created_subprogs_def]>>rw[]>>
  pairarg_tac>>gs[]>>FULL_CASE_TAC>>gs[]>>
  every_case_tac>>
  rveq>>gs[not_created_subprogs_def]>>
  rveq>>gs[not_created_subprogs_def,
           word_allocTheory.fake_move_def]>>metis_tac[]
QED

Theorem ssa_cc_trans_not_created_subprogs[local]:
  not_created_subprogs P prog ∧
  ssa_cc_trans prog ssa n = (prog', ssa', na)⇒
  not_created_subprogs P prog'
Proof
  MAP_EVERY qid_spec_tac [‘prog'’, ‘ssa'’, ‘na’, ‘n’, ‘ssa’, ‘prog’]>>
  recInduct word_allocTheory.ssa_cc_trans_ind>>
  rw[word_allocTheory.ssa_cc_trans_def,
     word_allocTheory.fix_inconsistencies_def,
     word_allocTheory.list_next_var_rename_move_def,
     not_created_subprogs_def]>>gs[]>>
  rpt (pairarg_tac>>gs[])>>rveq>>
  gs[word_allocTheory.ssa_cc_trans_def,
     word_allocTheory.fix_inconsistencies_def,
     word_allocTheory.list_next_var_rename_move_def,
     not_created_subprogs_def]
  >- (drule ssa_cc_trans_inst_not_created_subprogs>>rw[])
  >- (drule fake_moves_not_created_subprogs>>rw[])
  >- (EVERY_CASE_TAC>>gs[]>>rveq>>gs[not_created_subprogs_def]>>
    rpt (pairarg_tac>>gs[])>>rveq>>gs[not_created_subprogs_def]>>
    drule fake_moves_not_created_subprogs>>rw[])
QED

Theorem setup_ssa_not_created_subprogs[local]:
  not_created_subprogs P prog ∧
  setup_ssa n v prog = (mov, ssa, na)⇒
  not_created_subprogs P mov
Proof
  rw[word_allocTheory.setup_ssa_def]>>
  pairarg_tac>>gs[]>>
  rw[word_allocTheory.setup_ssa_def,
     word_allocTheory.list_next_var_rename_move_def,
     not_created_subprogs_def]
QED

Theorem full_ssa_cc_trans_not_created_subprogs[local]:
  not_created_subprogs P prog ⇒
  not_created_subprogs P (full_ssa_cc_trans n prog)
Proof
  rw[word_allocTheory.full_ssa_cc_trans_def]>>
  pairarg_tac>>gs[]>>
  pairarg_tac>>
  drule_all setup_ssa_not_created_subprogs>>
  rw[not_created_subprogs_def]>>
  drule_all ssa_cc_trans_not_created_subprogs>>
  rw[not_created_subprogs_def]
QED

Theorem word_get_code_labels_fake_moves[local]:
   ∀a b c d e f g h i.
   fake_moves prio a b c d = (e,f,g,h,i) ⇒
   word_get_code_labels e = {} ∧
   word_get_code_labels f = {}
Proof
  Induct \\ rw[fake_moves_def] \\ rw[]
  \\ pairarg_tac \\ fs[]
  \\ fs[CaseEq"option"] \\ rw[]
  \\ first_x_assum old_drule \\ rw[]
  \\ rw[fake_move_def]
QED

Theorem word_get_code_labels_ssa_cc_trans[local]:
   ∀x y z a b c.
   ssa_cc_trans x y z = (a,b,c) ⇒
   word_get_code_labels a = word_get_code_labels x
Proof
  recInduct ssa_cc_trans_ind
  \\ rw[ssa_cc_trans_def] \\ fs[]
  \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ fs[]
  >- (
    Cases_on`i` \\ fs[ssa_cc_trans_inst_def]
    \\ rveq \\ fs[]
    \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ fs[]
    \\ TRY(rename1`Arith arith` \\ Cases_on`arith`)
    \\ TRY(rename1`Mem memop _ dst` \\ Cases_on`memop` \\ Cases_on`dst`)
    \\ TRY(rename1`FP flop` \\ Cases_on`flop`)
    \\ fs[ssa_cc_trans_inst_def,CaseEq"reg_imm",CaseEq"bool"]
    \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ fs[] )
  >- (
    fs[fix_inconsistencies_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[]
    \\ imp_res_tac word_get_code_labels_fake_moves
    \\ rw[])
  >- (
    fs[list_next_var_rename_move_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[] )
  >- (
    fs[list_next_var_rename_move_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[] )
  >- (
    fs[list_next_var_rename_move_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[] )
  >- (
    fs[CaseEq"option"] \\ rveq \\ fs[]
    \\ fs[list_next_var_rename_move_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[]
    \\ fs[CaseEq"prod", fix_inconsistencies_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[]
    \\ imp_res_tac word_get_code_labels_fake_moves
    \\ fs[])
QED

Theorem word_get_code_labels_full_ssa_cc_trans[local]:
  ∀m p.
  word_get_code_labels (full_ssa_cc_trans m p) =
  word_get_code_labels p
Proof
  simp[full_ssa_cc_trans_def]
  \\ rpt gen_tac
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ fs[setup_ssa_def]
  \\ pairarg_tac \\ fs[]
  \\ rveq \\ fs[]
  \\ old_drule word_get_code_labels_ssa_cc_trans
  \\ rw[]
QED

Theorem word_good_handlers_fake_moves[local]:
   ∀a b c d e f g h i.
   fake_moves prio a b c d = (e,f,g,h,i) ⇒
   word_good_handlers n e ∧
   word_good_handlers n f
Proof
  Induct \\ rw[fake_moves_def] \\ rw[]
  \\ pairarg_tac \\ fs[]
  \\ fs[CaseEq"option"] \\ rw[]
  \\ first_x_assum old_drule \\ rw[]
  \\ rw[fake_move_def]
QED

Theorem word_good_handlers_ssa_cc_trans[local]:
   ∀x y z a b c.
   ssa_cc_trans x y z = (a,b,c) ⇒
   word_good_handlers n a = word_good_handlers n x
Proof
  recInduct ssa_cc_trans_ind
  \\ rw[ssa_cc_trans_def] \\ fs[]
  \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ fs[]
  >- (
    Cases_on`i` \\ fs[ssa_cc_trans_inst_def]
    \\ rveq \\ fs[]
    \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ fs[]
    \\ TRY(rename1`Arith arith` \\ Cases_on`arith`)
    \\ TRY(rename1`Mem memop _ dst` \\ Cases_on`memop` \\ Cases_on`dst`)
    \\ TRY(rename1`FP flop` \\ Cases_on`flop`)
    \\ fs[ssa_cc_trans_inst_def,CaseEq"reg_imm",CaseEq"bool"]
    \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ fs[] )
  >- (
    fs[fix_inconsistencies_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[]
    \\ imp_res_tac word_good_handlers_fake_moves
    \\ rw[])
  >- (
    fs[list_next_var_rename_move_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[] )
  >- (
    fs[list_next_var_rename_move_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[] )
  >- (
    fs[list_next_var_rename_move_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[] )
  >- (
    fs[CaseEq"option"] \\ rveq \\ fs[]
    \\ fs[list_next_var_rename_move_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[]
    \\ fs[CaseEq"prod", fix_inconsistencies_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[]
    \\ imp_res_tac word_good_handlers_fake_moves
    \\ fs[])
QED

Theorem word_good_handlers_full_ssa_cc_trans[local]:
  ∀m p.
  word_good_handlers n (full_ssa_cc_trans m p) ⇔
  word_good_handlers n p
Proof
  simp[full_ssa_cc_trans_def]
  \\ rpt gen_tac
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ fs[setup_ssa_def]
  \\ pairarg_tac \\ fs[]
  \\ rveq \\ fs[]
  \\ old_drule word_good_handlers_ssa_cc_trans
  \\ rw[]
QED

Theorem flat_exp_conventions_ShareInst[local]:
  flat_exp_conventions (ShareInst op v exp) <=>
    ((?v c. exp = Op Add [Var v;Const c]) \/ (?v. exp = Var v))
Proof
  eq_tac
  >- (
    gvs[DefnBase.one_line_ify NONE flat_exp_conventions_def] >>
    rpt (TOP_CASE_TAC >> simp[])) >>
  rw[] >>
  simp[flat_exp_conventions_def]
QED

Theorem flat_exp_conventions_fake_moves[local]:
  ∀ls ssal ssar na l r a b c conf.
  fake_moves prio ls ssal ssar na = (l,r,a,b,c) ⇒
  flat_exp_conventions l ∧
  flat_exp_conventions r
Proof
  Induct>>
  fs[fake_moves_def]>>rw[]>>
  fs[flat_exp_conventions_def]>>
  rpt(pairarg_tac>>gvs[])>>
  gvs[AllCaseEqs()]>>
  first_x_assum drule_all>>
  simp[flat_exp_conventions_def,fake_move_def]
QED

Theorem ssa_cc_trans_flat_exp_conventions[local]:
  ∀prog ssa na.
  flat_exp_conventions prog ⇒
  flat_exp_conventions (FST (ssa_cc_trans prog ssa na))
Proof
  ho_match_mp_tac ssa_cc_trans_ind>>full_simp_tac(srw_ss())[ssa_cc_trans_def]>>srw_tac[][]>>
  unabbrev_all_tac>>
  full_simp_tac(srw_ss())[flat_exp_conventions_def]
  >-
    (Cases_on`i`>>TRY(Cases_on`a`)>>TRY(Cases_on`m`)>>TRY(Cases_on`r`)>>
    TRY(Cases_on`f`)>>
    full_simp_tac(srw_ss())[ssa_cc_trans_inst_def,LET_THM,next_var_rename_def]>>
    every_case_tac>>rw[]>>
    fs[flat_exp_conventions_def])
  >-
    (pop_assum mp_tac>>full_simp_tac(srw_ss())[fix_inconsistencies_def,fake_moves_def]>>LET_ELIM_TAC>>full_simp_tac(srw_ss())[flat_exp_conventions_def]>>
    metis_tac[flat_exp_conventions_fake_moves,flat_exp_conventions_def])
  >-
    (full_simp_tac(srw_ss())[list_next_var_rename_move_def]>>rpt (pop_assum mp_tac)>>
    LET_ELIM_TAC>>full_simp_tac(srw_ss())[flat_exp_conventions_def,EQ_SYM_EQ])
  >-
    (Cases_on`exp`>>full_simp_tac(srw_ss())[ssa_cc_trans_exp_def,flat_exp_conventions_def])
  >-
    (full_simp_tac(srw_ss())[list_next_var_rename_move_def]>>rpt (pop_assum mp_tac)>>
    LET_ELIM_TAC>>full_simp_tac(srw_ss())[flat_exp_conventions_def,EQ_SYM_EQ])
  >-
    (fs[list_next_var_rename_move_def]>>rpt (pairarg_tac>>fs[])>>rw[]>>
    fs[flat_exp_conventions_def])
  >-
   (EVERY_CASE_TAC>>unabbrev_all_tac>>
     full_simp_tac(srw_ss())[flat_exp_conventions_def]
    >-
      (full_simp_tac(srw_ss())[list_next_var_rename_move_def]>>rpt (pop_assum mp_tac)>>
      LET_ELIM_TAC>>full_simp_tac(srw_ss())[flat_exp_conventions_def,EQ_SYM_EQ])
    >>
      LET_ELIM_TAC>>unabbrev_all_tac>>
      full_simp_tac(srw_ss())[list_next_var_rename_move_def,flat_exp_conventions_def]>>
      full_simp_tac(srw_ss())[fix_inconsistencies_def]>>
      rpt (pop_assum mp_tac)>> LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>
      metis_tac[flat_exp_conventions_fake_moves,flat_exp_conventions_def])
  >> (*ShareInst*)
    IF_CASES_TAC >>
    fs[flat_exp_conventions_ShareInst] >>
    simp[ssa_cc_trans_exp_def]
QED

Theorem full_ssa_cc_trans_flat_exp_conventions:
  ∀prog n.
  flat_exp_conventions prog ⇒
  flat_exp_conventions (full_ssa_cc_trans n prog)
Proof
  full_simp_tac(srw_ss())[full_ssa_cc_trans_def,setup_ssa_def,list_next_var_rename_move_def]>>
  LET_ELIM_TAC>>unabbrev_all_tac>>full_simp_tac(srw_ss())[flat_exp_conventions_def,EQ_SYM_EQ]>>
  metis_tac[ssa_cc_trans_flat_exp_conventions,FST]
QED

Theorem fake_moves_wf_cutsets[local]:
  ∀ls A B C L R D E G.
  fake_moves prio ls A B C = (L,R,D,E,G) ⇒
  wf_cutsets L ∧ wf_cutsets R
Proof
  Induct>>fs[fake_moves_def,wf_cutsets_def]>>rw[]>>
  pairarg_tac>>fs[]>>EVERY_CASE_TAC>>fs[]>>
  rveq>>fs[wf_cutsets_def,fake_move_def]>>
  metis_tac[]
QED
Theorem ssa_cc_trans_wf_cutsets[local]:
  ∀prog ssa na.
  let (prog',ssa',na') = ssa_cc_trans prog ssa na in
  wf_cutsets prog'
Proof
  ho_match_mp_tac ssa_cc_trans_ind>>
  rw[]>>
  fs[wf_cutsets_def,ssa_cc_trans_def,fix_inconsistencies_def,list_next_var_rename_move_def]>>
  rpt(pairarg_tac >> gvs[]) >> gvs[wf_cutsets_def] >>
  gvs[AllCaseEqs(),wf_cutsets_def,oneline ssa_cc_trans_inst_def, wf_fromAList] >>
  rpt(pairarg_tac >> gvs[]) >>
  gvs[wf_cutsets_def,wf_names_def,apply_nummaps_key_def,wf_fromAList]
  >>metis_tac[fake_moves_wf_cutsets]
QED

Theorem full_ssa_cc_trans_wf_cutsets:
  ∀n prog.
  wf_cutsets (full_ssa_cc_trans n prog)
Proof
  fs[full_ssa_cc_trans_def,setup_ssa_def,list_next_var_rename_move_def]>>
  rw[]>>pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  rveq>>fs[wf_cutsets_def]>>
  Q.ISPECL_THEN [`prog`,`ssa`,`n'`] assume_tac ssa_cc_trans_wf_cutsets>>
  rfs[]
QED

(*** remove_dead_prog ***)
val convs = [flat_exp_conventions_def,full_inst_ok_less_def,every_inst_def,pre_alloc_conventions_def,call_arg_convention_def,every_stack_var_def,every_var_def,extract_labels_def,wf_cutsets_def];

Theorem remove_dead_not_created_subprogs[local]:
  ∀prog q r.
  not_created_subprogs P prog ⇒
  not_created_subprogs P (FST (remove_dead prog q r))
Proof
  recInduct word_allocTheory.remove_dead_ind>>
  rw[word_allocTheory.remove_dead_def,
     not_created_subprogs_def]>>gs[]>>
  rw[word_allocTheory.remove_dead_def,
     not_created_subprogs_def]>>gs[]>>
  rpt (pairarg_tac>>gs[])>>rveq>>
  rw[not_created_subprogs_def]>>gs[]>>
  every_case_tac>>rpt (pairarg_tac>>gs[])>>rveq>>
  rw[not_created_subprogs_def]>>gs[]
QED

Theorem remove_dead_prog_not_created_subprogs[local]:
  not_created_subprogs P prog ⇒
  not_created_subprogs P (remove_dead_prog prog)
Proof
  simp[word_allocTheory.remove_dead_prog_def]>>
  metis_tac[remove_dead_not_created_subprogs]
QED

Theorem remove_dead_conventions[local]:
  ∀p live nlive c k.
    let comp = FST (remove_dead p live nlive) in
    (flat_exp_conventions p ⇒ flat_exp_conventions comp) ∧
    (full_inst_ok_less c p ⇒ full_inst_ok_less c comp) ∧
    (pre_alloc_conventions p ⇒ pre_alloc_conventions comp) ∧
    (every_inst P p ⇒ every_inst P comp) ∧
    (wf_cutsets p ⇒ wf_cutsets comp) ∧
    (extract_labels p = extract_labels comp)
Proof
  ho_match_mp_tac remove_dead_ind>>rw[]>>
  fs[remove_dead_def]>>
  rpt IF_CASES_TAC>>fs convs>>
  rpt(pairarg_tac>>fs[])>>
  rw[]>> fs convs>>
  EVERY_CASE_TAC>>fs convs
QED

Theorem remove_dead_prog_conventions =
  (remove_dead_conventions |> Q.SPEC`p` |> Q.SPEC`LN` |> Q.SPEC`[]` |> SPEC_ALL |>
    SIMP_RULE std_ss [LET_THM,FORALL_AND_THM,GSYM remove_dead_prog_def]);

Theorem word_get_code_labels_remove_dead[local]:
  ∀ps live nlive.
  word_get_code_labels (FST (remove_dead ps live nlive)) ⊆
  word_get_code_labels ps
Proof
  ho_match_mp_tac remove_dead_ind>>rw[]>>
  fs[remove_dead_def]>>
  every_case_tac>>fs[]>>
  rpt(pairarg_tac>>fs[])>>rw[]>>
  fs[SUBSET_DEF]
QED

Theorem word_get_code_labels_remove_dead_prog[local]:
  word_get_code_labels (remove_dead_prog ps) ⊆
  word_get_code_labels ps
Proof
  simp[remove_dead_prog_def,word_get_code_labels_remove_dead]
QED

Theorem word_good_handlers_remove_dead[local]:
  ∀ps live nlive.
  word_good_handlers n (FST (remove_dead ps live nlive)) ⇔
  word_good_handlers n ps
Proof
  ho_match_mp_tac remove_dead_ind>>rw[]>>
  fs[remove_dead_def]>>
  every_case_tac>>fs[]>>
  rpt(pairarg_tac>>fs[])>>rw[]>>
  rw[]>>gvs[]
QED

Theorem word_good_handlers_remove_dead_prog[local]:
  word_good_handlers n (remove_dead_prog ps) ⇔
  word_good_handlers n ps
Proof
  simp[remove_dead_prog_def,word_good_handlers_remove_dead]
QED

(*** word_common_subexp_elim ***)
Theorem word_cse_extract_labels[local]:
  ∀p d d1 p1.
  word_cse d p = (d1,p1) ⇒
  extract_labels p1 = extract_labels p
Proof
  Induct \\ fs [word_cse_def,extract_labels_def] \\ rw []
  \\ rpt (pairarg_tac \\ gvs [])
  \\ fs [extract_labels_def]
  \\ res_tac \\ gvs [AllCaseEqs()]
  \\ fs [extract_labels_def,PULL_EXISTS]
  \\ every_case_tac \\ fs []
  \\ gvs [add_to_data_aux_def,AllCaseEqs(),extract_labels_def]
  \\ rename [‘word_cseInst d i = (d1,p)’]
  \\ Cases_on ‘i’
  \\ gvs [word_cseInst_def,extract_labels_def,AllCaseEqs(),add_to_data_def,
         add_to_data_aux_def]
  \\ Cases_on ‘a’
  \\ gvs [word_cseInst_def,extract_labels_def,AllCaseEqs(),add_to_data_def,
         add_to_data_aux_def]
QED

Theorem extract_labels_word_common_subexp_elim:
  extract_labels (word_common_subexp_elim p) = extract_labels p
Proof
  fs [word_common_subexp_elim_def] \\ pairarg_tac \\ rw []
  \\ drule word_cse_extract_labels \\ fs []
QED

Theorem word_cseInst_not_created_subprogs[local]:
  !env i. not_created_subprogs P (SND (word_cseInst env i))
Proof
  ho_match_mp_tac word_cseTheory.word_cseInst_ind
  \\ rw [word_cseTheory.word_cseInst_def]
  \\ fs [not_created_subprogs_def]
  \\ fs [word_cseTheory.add_to_data_def, word_cseTheory.add_to_data_aux_def]
  \\ every_case_tac
  \\ fs [not_created_subprogs_def]
QED

Theorem word_cse_not_created_subprogs[local]:
   !p env. not_created_subprogs P p ==>
   not_created_subprogs P (SND (word_cse env p))
Proof
  Induct \\ rw [word_cseTheory.word_cse_def]
  \\ fs [not_created_subprogs_def, word_cseInst_not_created_subprogs]
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [not_created_subprogs_def]
  \\ gvs [PAIR_FST_SND_EQ]
  \\ fs [word_cseTheory.add_to_data_aux_def]
  \\ every_case_tac
  \\ fs [not_created_subprogs_def, word_cseInst_not_created_subprogs]
QED

Theorem word_common_subexp_elim_not_created_subprogs[local]:
  not_created_subprogs P prog ⇒
  not_created_subprogs P (word_common_subexp_elim prog)
Proof
  fs [word_cseTheory.word_common_subexp_elim_def]
  \\ simp [ELIM_UNCURRY, word_cse_not_created_subprogs]
QED

Theorem word_good_handlers_word_common_subexp_elim[local]:
  word_good_handlers q (word_common_subexp_elim p) ⇔
  word_good_handlers q p
Proof
  fs [word_common_subexp_elim_def]
  \\ pairarg_tac \\ fs []
  \\ rename [‘_ k _ = (a,np)’]
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘k’
  \\ qid_spec_tac ‘a’
  \\ qid_spec_tac ‘np’
  \\ qid_spec_tac ‘q’
  \\ qid_spec_tac ‘p’
  \\ Induct \\ fs [word_cse_def]
  \\ rw [] \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [AllCaseEqs()]
  \\ res_tac \\ fs []
  \\ gvs [add_to_data_aux_def,AllCaseEqs()]
  \\ gvs [word_cseInst_def |> DefnBase.one_line_ify NONE,AllCaseEqs()]
  \\ gvs [add_to_data_def,add_to_data_aux_def,AllCaseEqs()]
  \\ rename1`xx = (_,_)`
  \\ Cases_on`xx` \\ simp[]
QED

Theorem word_get_code_labels_word_common_subexp_elim[local]:
  word_get_code_labels (word_common_subexp_elim p) =
  word_get_code_labels p
Proof
  fs [word_common_subexp_elim_def]
  \\ pairarg_tac \\ fs []
  \\ rename [‘_ k _ = (a,np)’]
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘k’
  \\ qid_spec_tac ‘a’
  \\ qid_spec_tac ‘np’
  \\ qid_spec_tac ‘q’
  \\ qid_spec_tac ‘p’
  \\ Induct \\ fs [word_cse_def]
  \\ rw [] \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [AllCaseEqs()]
  \\ res_tac \\ fs []
  \\ gvs [add_to_data_aux_def,AllCaseEqs()]
  \\ gvs [word_cseInst_def |> DefnBase.one_line_ify NONE,AllCaseEqs()]
  \\ gvs [add_to_data_def,add_to_data_aux_def,AllCaseEqs()]
QED

Theorem word_cse_flat_exp_conventions[local]:
  ∀p data.
    let p' = SND (word_cse data p) in
      flat_exp_conventions p ⇒ flat_exp_conventions p'
Proof
  Induct \\ rw[]
  \\ gvs [flat_exp_conventions_def, word_cse_def, AllCaseEqs()]
  \\ rpt (pairarg_tac >> gvs[])
  \\ gvs [flat_exp_conventions_def, word_cse_def,
   oneline word_cseInst_def,add_to_data_def,
   add_to_data_aux_def,
  oneline canonicalExp_def, AllCaseEqs()]
  \\ EVERY_CASE_TAC \\ gvs[flat_exp_conventions_def]
  >-(
 first_x_assum (qspec_then `data` assume_tac) \\ gvs[])
  >-(
 last_x_assum (qspec_then `data` assume_tac) >>
 last_x_assum (qspec_then `data1` assume_tac)
 \\ gvs[])
  >-(
 last_x_assum (qspec_then `data` assume_tac) >>
 last_x_assum (qspec_then `data` assume_tac)
 \\ gvs[])
QED

Theorem flat_exp_conventions_word_common_subexp_elim:
  flat_exp_conventions p ⇒
  flat_exp_conventions (word_common_subexp_elim p)
Proof
  fs [word_common_subexp_elim_def] \\ pairarg_tac \\ gvs []
  \\ qspecl_then [‘p’,‘empty_data’] mp_tac word_cse_flat_exp_conventions
  \\ fs []
QED

Theorem word_cse_wf_cutsets[local]:
  ∀p data.
    let p' = SND (word_cse data p) in
      wf_cutsets p ⇒ wf_cutsets p'
Proof
  Induct \\ rw[] \\
  rpt (pairarg_tac \\ gvs[]) \\
  gvs [flat_exp_conventions_def, word_cse_def,
   oneline word_cseInst_def,add_to_data_def,
   add_to_data_aux_def,
  oneline canonicalExp_def,wf_cutsets_def, AllCaseEqs()] \\
  rpt (pairarg_tac \\ gvs[]) \\
  gvs [wf_cutsets_def, word_cse_def, AllCaseEqs()] \\
  every_case_tac \\ gvs[wf_cutsets_def]
  >-(
 first_x_assum (qspec_then `data` assume_tac) \\ gvs[])
  >-(
 last_x_assum (qspec_then `data` assume_tac) >>
 last_x_assum (qspec_then `data1` assume_tac)
 \\ gvs[])
  >-(
 last_x_assum (qspec_then `data` assume_tac) >>
 last_x_assum (qspec_then `data` assume_tac)
 \\ gvs[])
QED

Theorem wf_cutsets_word_common_subexp_elim:
  wf_cutsets p ⇒ wf_cutsets (word_common_subexp_elim p)
Proof
  fs [word_common_subexp_elim_def] \\ pairarg_tac \\ gvs []
  \\ qspecl_then [‘p’,‘empty_data’] mp_tac word_cse_wf_cutsets
  \\ fs []
QED


(*** copy_prop ***)

(* may not prove goal fully *)
fun boring_tac def =
  ho_match_mp_tac copy_prop_prog_ind
  >>rw[copy_prop_prog_def,def]
  >>rpt(pairarg_tac>>fs[])
  >>rw[def]
  >-(
    qid_spec_tac‘cs’>>qid_spec_tac‘i’
    >>ho_match_mp_tac copy_prop_inst_ind
    >>rw[copy_prop_inst_def,def]
  )
  >-(
    TOP_CASE_TAC>>rw[def]
  )
  >- (
    every_case_tac>>simp[def]>>
    pairarg_tac>>simp[def]
  );

Theorem wf_cutsets_copy_prop_aux[local]:
  ∀p cs. wf_cutsets p ⇒
    wf_cutsets (FST (copy_prop_prog p cs))
Proof
  boring_tac wf_cutsets_def
QED

Theorem wf_cutsets_copy_prop:
  wf_cutsets p ⇒ wf_cutsets (copy_prop p)
Proof
  metis_tac[wf_cutsets_copy_prop_aux,copy_prop_def]
QED

Theorem every_inst_distinct_tar_reg_copy_prop_aux[local]:
  ∀p cs.
  every_inst distinct_tar_reg p ⇒
  every_inst distinct_tar_reg (FST (copy_prop_prog p cs))
Proof
  ho_match_mp_tac copy_prop_prog_ind
  >>rw[every_inst_def,copy_prop_prog_def]
  >>rpt(pairarg_tac>>fs[])
  >>rw[every_inst_def]
  (* Inst *)
  >-(
    pop_assum mp_tac
    >>qid_spec_tac‘cs’>>qid_spec_tac‘i’
    >>ho_match_mp_tac copy_prop_inst_ind
    >>rw[copy_prop_inst_def,every_inst_def,distinct_tar_reg_def]
  )
  >-fs[distinct_tar_reg_def]
  >- (TOP_CASE_TAC>>rw[every_inst_def,distinct_tar_reg_def])
  >- (
    every_case_tac>>fs[every_inst_def]>>
    pairarg_tac>>simp[every_inst_def])
QED

Theorem every_inst_distinct_tar_reg_copy_prop:
  every_inst distinct_tar_reg p ⇒
  every_inst distinct_tar_reg (copy_prop p)
Proof
  metis_tac[every_inst_distinct_tar_reg_copy_prop_aux,copy_prop_def]
QED

Theorem extract_labels_copy_prop_aux[local]:
  ∀p cs.
  extract_labels (FST (copy_prop_prog p cs)) =
  extract_labels p
Proof
  boring_tac extract_labels_def
QED

Theorem extract_labels_copy_prop:
  extract_labels (copy_prop p) =
  extract_labels p
Proof
  metis_tac[extract_labels_copy_prop_aux,copy_prop_def]
QED

Theorem flat_exp_conventions_copy_prop_aux[local]:
  ∀p cs.
  flat_exp_conventions p ⇒
  flat_exp_conventions (FST (copy_prop_prog p cs))
Proof
  boring_tac flat_exp_conventions_def
  >>Cases_on‘exp’
  >>fs[copy_prop_share_def,flat_exp_conventions_def]
  >>rpt(TOP_CASE_TAC>>rw[flat_exp_conventions_def])
QED

Theorem flat_exp_conventions_copy_prop:
  flat_exp_conventions p ⇒
  flat_exp_conventions (copy_prop p)
Proof
  metis_tac[flat_exp_conventions_copy_prop_aux,copy_prop_def]
QED

Theorem copy_prop_prog_not_alloc_var_aux1[local]:
  (∀x. ¬is_alloc_var x ⇒ lookup x cs.to_eq = NONE) ⇒
  ¬is_alloc_var x ⇒
  lookup x (remove_eq cs y).to_eq = NONE
Proof
  rw[remove_eq_def]>>TOP_CASE_TAC>>rw[empty_eq_def]
QED

Theorem copy_prop_prog_not_alloc_var_aux2[local]:
  ∀cs.
  (∀x. ¬is_alloc_var x ⇒ lookup x cs.to_eq = NONE) ⇒
  ¬is_alloc_var x ⇒
  lookup x (remove_eqs cs yy).to_eq = NONE
Proof
  Induct_on‘yy’>>rw[remove_eqs_def]
  >>metis_tac[copy_prop_prog_not_alloc_var_aux1]
QED

(* trivial and tedious *)
Theorem copy_prop_prog_not_alloc_var[local]:
  ∀p cs.
  (∀x. ¬(is_alloc_var x) ⇒ lookup x cs.to_eq = NONE) ⇒
  (∀x. ¬(is_alloc_var x) ⇒ lookup x (SND (copy_prop_prog p cs)).to_eq = NONE)
Proof
  ho_match_mp_tac copy_prop_prog_ind
  >>rw[copy_prop_prog_def]
  >>rpt(pairarg_tac>>fs[])
  >>rw[empty_eq_def,copy_prop_prog_not_alloc_var_aux1,copy_prop_prog_not_alloc_var_aux2]
  >-(
    pop_assum mp_tac
    >>qpat_x_assum‘EVERY _ _’kall_tac
    >>qid_spec_tac‘xs'’>>qid_spec_tac‘cs'’
    >>Induct_on‘xs’
    >-(fs[copy_prop_move_def]>>metis_tac[])
    >>rw[copy_prop_move_def]
    >>PairCases_on‘h’
    >>fs[copy_prop_move_def]
    >>(pairarg_tac>>fs[])
    >>gvs[]
    >>rw[set_eq_def](*2*)
    >-(
      TOP_CASE_TAC(*2*)
      >-(
        rw[lookup_insert]
        >-metis_tac[]
        >-metis_tac[]
        >>rw[remove_eq_def]
        >>TOP_CASE_TAC>>rw[empty_eq_def]
      )
      >-(
        rw[lookup_insert]
        >-metis_tac[]
        >>rw[remove_eq_def]
        >>TOP_CASE_TAC>>rw[empty_eq_def]
      )
    )
    >>rw[remove_eq_def]
    >>TOP_CASE_TAC>>rw[empty_eq_def]
  )
  >-(
    rpt(pop_assum mp_tac)
    >>qid_spec_tac‘cs’>>qid_spec_tac‘i’
    >>ho_match_mp_tac copy_prop_inst_ind
    >>rw[copy_prop_inst_def]
    >>metis_tac[copy_prop_prog_not_alloc_var_aux1,copy_prop_prog_not_alloc_var_aux2]
  )
  >-rw[merge_eqs_def,lookup_inter_eq]
  >- (
    TOP_CASE_TAC>>rw[]>>
    simp[set_store_eq_def]>>
    every_case_tac>>gvs[lookup_insert]
    >- metis_tac[]
    >- simp[empty_eq_def]
    >- metis_tac[]
  )
  >- (
    gvs[remove_eq_def]>>every_case_tac>>simp[empty_eq_def]>>
    pairarg_tac>>gvs[copy_prop_move_def,set_eq_def,remove_eq_def]>>
    every_case_tac>>rw[lookup_insert,empty_eq_def]>>
    metis_tac[])
QED

Theorem pre_alloc_conventions_copy_prop_aux[local]:
  ∀p cs.
  (∀x. ¬(is_alloc_var x) ⇒ lookup x cs.to_eq = NONE) ⇒
  pre_alloc_conventions p ⇒
  pre_alloc_conventions (FST (copy_prop_prog p cs))
Proof
  ho_match_mp_tac copy_prop_prog_ind
  >> rpt conj_tac >> rpt (gen_tac ORELSE disch_tac)
  >> fs[copy_prop_prog_def,pre_alloc_conventions_def,COND_RAND]
  >> rpt(pairarg_tac>>fs[])
  >> fs[wordLangTheory.every_stack_var_def,call_arg_convention_def]
  >~[`copy_prop_inst`]
  >-(
    rpt $ pop_assum mp_tac >>
    qid_spec_tac‘cs’>>qid_spec_tac‘i’
    >> ho_match_mp_tac copy_prop_inst_ind
    >> rpt conj_tac >> rpt (gen_tac ORELSE disch_tac)
    >> fs[copy_prop_inst_def,wordLangTheory.every_stack_var_def,
       inst_arg_convention_def, call_arg_convention_def]
    >- fs[reg_allocTheory.is_alloc_var_def,lookup_eq_def]
    >> rpt(pairarg_tac>>fs[]) >> rw[]
    >> fs[copy_prop_inst_def,wordLangTheory.every_stack_var_def,
       inst_arg_convention_def, call_arg_convention_def]
  )
  >- (qpat_abbrev_tac `ysl = LENGTH _` >> gvs[] >>
  fs[MAP_GENLIST,GENLIST_FUN_EQ] >>
  rw[] >>
  fs[lookup_eq_def,reg_allocTheory.is_alloc_var_def] >>
  first_assum (qspec_then `(2 * (x + 1))` mp_tac) >>
  impl_tac >-intLib.ARITH_TAC >> gvs[])
  >- rw[lookup_eq_def,reg_allocTheory.is_alloc_var_def,copy_prop_prog_not_alloc_var]
  >-(
    ‘cs' = SND (copy_prop_prog p cs)’ by rw[]
    >>rw[]
    >>metis_tac[copy_prop_prog_not_alloc_var]
  )
  >-(TOP_CASE_TAC>>
    rw[wordLangTheory.every_stack_var_def,
    call_arg_convention_def])
  >- (
    every_case_tac>>
    TRY(pairarg_tac)>>
    simp[every_stack_var_def,call_arg_convention_def])
QED

Theorem pre_alloc_conventions_copy_prop:
  pre_alloc_conventions p ⇒
  pre_alloc_conventions (copy_prop p)
Proof
  ‘∀x. lookup x empty_eq.to_eq = NONE’ by rw[empty_eq_def]
  >>metis_tac[pre_alloc_conventions_copy_prop_aux,copy_prop_def]
QED

Theorem full_inst_ok_less_copy_prop_aux[local]:
  ∀p cs.
  full_inst_ok_less ac p ⇒
  full_inst_ok_less ac (FST (copy_prop_prog p cs))
Proof
  ho_match_mp_tac copy_prop_prog_ind
  >> rw[copy_prop_prog_def,full_inst_ok_less_def]
  >> rpt(pairarg_tac>>fs[])
  >> rw[full_inst_ok_less_def]
  >- (
    pop_assum mp_tac
    >>qid_spec_tac‘cs’>>qid_spec_tac‘i’
    >>ho_match_mp_tac copy_prop_inst_ind
    >>rw[copy_prop_inst_def,full_inst_ok_less_def]
    >>fs[inst_ok_less_def]
    >-(
      Cases_on‘ri’
      >>fs[inst_ok_less_def,lookup_eq_imm_def]
    )
    >-(
      Cases_on‘ri’
      >>fs[inst_ok_less_def,lookup_eq_imm_def]
    )
    >>metis_tac[]
  )
  >- (TOP_CASE_TAC>>rw[full_inst_ok_less_def])
  >- (
    every_case_tac>>TRY(pairarg_tac)>>fs[full_inst_ok_less_def]
    )
  >- (
    rw[copy_prop_share_def]>>every_case_tac
    >>gvs[wordLangTheory.exp_to_addr_def]
  )
QED

Theorem full_inst_ok_less_copy_prop:
  full_inst_ok_less ac p ⇒
  full_inst_ok_less ac (copy_prop p)
Proof
  metis_tac[full_inst_ok_less_copy_prop_aux,copy_prop_def]
QED

Theorem word_get_code_labels_copy_prop[local]:
  word_get_code_labels (copy_prop ps) =
  word_get_code_labels ps
Proof
  simp[copy_prop_def]
  \\ qmatch_goalsub_abbrev_tac  `copy_prop_prog ps s`
  \\ qid_spec_tac ‘s’
  \\ qid_spec_tac ‘ps’
  \\ ho_match_mp_tac copy_prop_prog_ind
  \\ unabbrev_all_tac \\ simp[copy_prop_prog_def]
  \\ rw [] \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [AllCaseEqs()]
  \\ res_tac \\ fs []
  >-
    (simp[oneline copy_prop_inst_def] \\ every_case_tac \\ fs[])
  >- (every_case_tac \\ fs[])
  >- (every_case_tac \\ TRY (pairarg_tac) \\ fs[])
QED

Theorem word_good_handlers_copy_prop[local]:
  word_good_handlers n (copy_prop ps) ⇔
  word_good_handlers n ps
Proof
  simp[copy_prop_def]
  \\ qmatch_goalsub_abbrev_tac  `copy_prop_prog ps s`
  \\ qid_spec_tac ‘s’
  \\ qid_spec_tac ‘ps’
  \\ ho_match_mp_tac copy_prop_prog_ind
  \\ unabbrev_all_tac \\ simp[copy_prop_prog_def]
  \\ rw [] \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [AllCaseEqs()]
  \\ res_tac \\ fs []
  >-
    (simp[oneline copy_prop_inst_def] \\ every_case_tac \\ fs[])
  >- (every_case_tac \\ fs[])
  >- (every_case_tac \\ TRY (pairarg_tac) \\ fs[])
QED

Theorem copy_prop_not_created_subprogs[local]:
  not_created_subprogs P prog ⇒
  not_created_subprogs P (copy_prop prog)
Proof
  simp[copy_prop_def]
  \\ qmatch_goalsub_abbrev_tac  `copy_prop_prog ps s`
  \\ qid_spec_tac `s`
  \\ qid_spec_tac `ps`
  \\ ho_match_mp_tac copy_prop_prog_ind
  \\ unabbrev_all_tac \\ simp[copy_prop_prog_def,not_created_subprogs_def]
  \\ rw[] \\ rpt (pairarg_tac \\ gvs[])
  \\ fs[not_created_subprogs_def]
  >- (simp[oneline copy_prop_inst_def] \\ every_case_tac \\
    fs[not_created_subprogs_def])
  >- (every_case_tac \\ fs[not_created_subprogs_def])
  >- (every_case_tac \\ TRY pairarg_tac \\ fs[not_created_subprogs_def])
QED

(*** three_to_to_reg_prog ***)
Theorem three_to_two_reg_prog_lab_pres:
  ∀prog.
  extract_labels prog = extract_labels (three_to_two_reg_prog b prog)
Proof
  simp[three_to_two_reg_prog_def]>>
  ho_match_mp_tac three_to_two_reg_ind>>
  rw[three_to_two_reg_def,extract_labels_def]>>EVERY_CASE_TAC>>fs[]
QED

Theorem three_to_two_reg_prog_not_created_subprogs[local]:
  ∀prog.
  not_created_subprogs P prog ⇒
  not_created_subprogs P (three_to_two_reg_prog b prog)
Proof
  simp[three_to_two_reg_prog_def]>>
  ho_match_mp_tac three_to_two_reg_ind>>
  rw[three_to_two_reg_def,not_created_subprogs_def]>>
  gs[]>>every_case_tac>>gs[]
QED

Theorem three_to_two_reg_prog_two_reg_inst:
  ∀prog.
  b ⇒
  every_inst two_reg_inst (three_to_two_reg_prog b prog)
Proof
  simp[three_to_two_reg_prog_def]>>
  ho_match_mp_tac three_to_two_reg_ind>>
  rw[]>>fs[every_inst_def,two_reg_inst_def,three_to_two_reg_def,LET_THM]>>
  EVERY_CASE_TAC>>
  fs[]
QED

Theorem three_to_two_reg_prog_wf_cutsets:
  ∀prog.
  wf_cutsets prog ⇒ wf_cutsets (three_to_two_reg_prog b prog)
Proof
  simp[three_to_two_reg_prog_def]>>
  ho_match_mp_tac three_to_two_reg_ind>>
  rw[]>>
  fs[wf_cutsets_def,three_to_two_reg_def]>>
  EVERY_CASE_TAC>>fs[]
QED

Theorem three_to_two_reg_prog_pre_alloc_conventions:
  ∀prog.
  pre_alloc_conventions prog ⇒
  pre_alloc_conventions (three_to_two_reg_prog b prog)
Proof
  simp[three_to_two_reg_prog_def]>>
  ho_match_mp_tac three_to_two_reg_ind>>
  rw[]>>
  fs[every_stack_var_def,pre_alloc_conventions_def,every_inst_def,three_to_two_reg_def,call_arg_convention_def,inst_arg_convention_def,two_reg_inst_def]>>
  FULL_CASE_TAC>>fs[]>>
  PairCases_on`x`>>fs[]>>
  FULL_CASE_TAC>>fs[]>>
  PairCases_on`x`>>fs[]
QED

Theorem three_to_two_reg_prog_flat_exp_conventions:
  ∀prog.
  flat_exp_conventions prog ⇒
  flat_exp_conventions (three_to_two_reg_prog b prog)
Proof
  simp[three_to_two_reg_prog_def]>>
  ho_match_mp_tac three_to_two_reg_ind>>
  rw[]>>
  full_simp_tac(srw_ss())[flat_exp_conventions_def,three_to_two_reg_def,LET_THM]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]
QED

Theorem three_to_two_reg_prog_full_inst_ok_less:
  ∀prog. full_inst_ok_less c prog ⇒
         full_inst_ok_less c (three_to_two_reg_prog b prog)
Proof
  simp[three_to_two_reg_prog_def] >>
  ho_match_mp_tac three_to_two_reg_ind>>srw_tac[][]>>
  full_simp_tac(srw_ss())[three_to_two_reg_def,LET_THM]>>EVERY_CASE_TAC>>fs[full_inst_ok_less_def]
  >-
    (Cases_on`bop`>>Cases_on`ri`>>fs[full_inst_ok_less_def,inst_ok_less_def,every_inst_def])
  >-
    (Cases_on`n`>>fs[inst_ok_less_def])
  >>
    metis_tac[inst_ok_less_def]
QED

Theorem word_get_code_labels_three_to_two_reg_prog[local]:
  ∀ps.
  word_get_code_labels (three_to_two_reg_prog b ps) =
  word_get_code_labels ps
Proof
  simp[three_to_two_reg_prog_def]>>
  ho_match_mp_tac three_to_two_reg_ind>>rw[]>>
  fs[three_to_two_reg_def]>>
  every_case_tac>>fs[]
QED

Theorem word_good_handlers_three_to_two_reg_prog[local]:
  ∀ps.
  word_good_handlers n (three_to_two_reg_prog b ps) ⇔
  word_good_handlers n ps
Proof
  simp[three_to_two_reg_prog_def]>>
  ho_match_mp_tac three_to_two_reg_ind>>rw[]>>
  fs[three_to_two_reg_def]>>
  every_case_tac>>fs[]
QED

(*** remove_unreach ***)
Theorem word_get_code_labels_dest_Seq_Move[local]:
  ∀p.
  dest_Seq_Move p = SOME (x,y,z) ⇒
  word_get_code_labels z = word_get_code_labels p
Proof
  ho_match_mp_tac dest_Seq_Move_ind>>rw[]>>
  gvs[dest_Seq_Move_def]
QED

Theorem word_get_code_labels_SimpSeq[local]:
  word_get_code_labels (SimpSeq p q) ⊆
  word_get_code_labels p ∪ word_get_code_labels q
Proof
  rw[SimpSeq_def]>>
  every_case_tac>>simp[]>>
  every_case_tac>>simp[SUBSET_DEF]>>
  drule word_get_code_labels_dest_Seq_Move>>
  simp[SUBSET_DEF]
QED

Theorem word_get_code_labels_Seq_assoc_right[local]:
  ∀ps qs.
  word_get_code_labels (Seq_assoc_right ps qs) ⊆
  word_get_code_labels ps ∪ word_get_code_labels qs
Proof
  ho_match_mp_tac Seq_assoc_right_ind >>
  simp[Seq_assoc_right_def] >>
  rw[] >> every_case_tac >> fs[]
  >- (irule SUBSET_TRANS >>
  first_x_assum (irule_at Any) >>
  fs[UNION_SUBSET] >>
  CONJ_TAC >- fs[GSYM UNION_ASSOC] >>
  irule SUBSET_TRANS >>
  first_x_assum (irule_at Any) >>
  fs[UNION_SUBSET] >>
  fs[Once UNION_COMM] >>
  fs[UNION_ASSOC])
  >> TRY  (
  irule SUBSET_TRANS >>
  irule_at Any word_get_code_labels_SimpSeq >>
  rw[] >>
  irule SUBSET_TRANS >>
  first_x_assum (irule_at Any) >>
   metis_tac[UNION_ASSOC,SUBSET_UNION,SUBSET_TRANS]
  )
  >>
  metis_tac[UNION_ASSOC,SUBSET_UNION,SUBSET_TRANS]
QED

Theorem word_get_code_labels_remove_unreach[local]:
  word_get_code_labels (remove_unreach ps) ⊆
  word_get_code_labels ps
Proof
  simp[remove_unreach_def]>>
  irule SUBSET_TRANS>>
  irule_at Any word_get_code_labels_Seq_assoc_right>>
  simp[]
QED

Theorem word_good_handlers_SimpSeq[local]:
  word_good_handlers n ps /\ word_good_handlers n qs ⇒
  word_good_handlers n (SimpSeq ps qs)
Proof
  qid_spec_tac ‘ps’ \\
  Induct \\ simp[SimpSeq_def] \\
  Cases_on `qs = Skip` \\ fs[] \\
  fs[oneline dest_Seq_Move_def] \\
  every_case_tac \\ fs[]
QED

Theorem word_good_handlers_Seq_assoc_right[local]:
  word_good_handlers n ps /\ word_good_handlers n qs ⇒
  word_good_handlers n (Seq_assoc_right ps qs)
Proof
  qid_spec_tac ‘qs’
  \\ qid_spec_tac ‘ps’
  \\ ho_match_mp_tac Seq_assoc_right_ind
  \\ simp[Seq_assoc_right_def]
  \\ rw[] \\ every_case_tac \\ fs[]
  \\ irule word_good_handlers_SimpSeq
  \\ fs[]
QED

Theorem word_good_handlers_remove_unreach[local]:
  word_good_handlers n ps ⇒
  word_good_handlers n (remove_unreach ps)
Proof
  simp[remove_unreach_def] \\ disch_tac \\
  irule word_good_handlers_Seq_assoc_right \\
  fs[]
  \\ qmatch_goalsub_abbrev_tac `Seq_assoc_right ps s`
  \\ qid_spec_tac ‘s’
  \\ qid_spec_tac ‘ps’
  \\ ho_match_mp_tac Seq_assoc_right_ind
  \\ unabbrev_all_tac \\ simp[Seq_assoc_right_def]
  \\ simp[SimpSeq_def]
  \\ rw[]
 \\ every_case_tac \\ fs[]
QED

Theorem SimpSeq_not_created_subprogs[local]:
  not_created_subprogs P ps /\ not_created_subprogs P qs ⇒
  not_created_subprogs P (SimpSeq ps qs)
Proof
 qid_spec_tac `ps` \\
 Induct \\ simp[SimpSeq_def,not_created_subprogs_def] \\
 Cases_on `qs = Skip` \\ fs[not_created_subprogs_def] \\
 fs[oneline dest_Seq_Move_def] \\
 every_case_tac \\  fs[not_created_subprogs_def]
QED

Theorem Seq_assoc_right_not_created_subprogs[local]:
  not_created_subprogs P ps /\ not_created_subprogs P qs ⇒
  not_created_subprogs P (Seq_assoc_right ps qs)
Proof
 qid_spec_tac `qs`
 \\ qid_spec_tac `ps`
 \\ ho_match_mp_tac Seq_assoc_right_ind
 \\ simp[Seq_assoc_right_def]
 \\ rw[] \\ every_case_tac \\ fs[]
 >- (first_x_assum (irule_at Any) \\ fs[not_created_subprogs_def])
 \\ irule SimpSeq_not_created_subprogs
 \\ fs[not_created_subprogs_def]
QED

Theorem remove_unreach_not_created_subprogs[local]:
  not_created_subprogs P prog ⇒
  not_created_subprogs P (remove_unreach prog)
Proof
  simp[remove_unreach_def] \\ disch_tac \\
  irule Seq_assoc_right_not_created_subprogs \\
  fs[not_created_subprogs_def]
QED

Theorem extract_labels_SimpSeq[local]:
  set (extract_labels (SimpSeq p1 p2)) ⊆  set (extract_labels (Seq p1 p2))
Proof
  rw [SimpSeq_def,extract_labels_def]
  \\ Cases_on ‘p1’ \\ rw [extract_labels_def] \\ gvs [SUBSET_DEF]
  \\ Cases_on ‘dest_Seq_Move p2’ \\ gvs []
  \\ rw [extract_labels_def] \\ gvs [SUBSET_DEF]
  \\ PairCases_on ‘x’ \\ gvs []
  \\ pop_assum mp_tac \\ rw []
  \\ gvs [oneline dest_Seq_Move_def, AllCaseEqs(), extract_labels_def]
QED

Theorem  extract_labels_Seq_assoc_right_lemma[local]:
  ∀p1 p2. set (extract_labels (Seq_assoc_right p1 p2)) ⊆
          set (extract_labels p1) ∪ set (extract_labels p2)
Proof
  HO_MATCH_MP_TAC Seq_assoc_right_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_right_def,extract_labels_def,extract_labels_SimpSeq]
  >- (
    gvs[SUBSET_DEF]
    \\ metis_tac[])
  >~ [`Call`]
  >- (
    every_case_tac \\ gvs[extract_labels_def]
    \\ irule SUBSET_TRANS
    \\ irule_at Any extract_labels_SimpSeq
    \\ fs [Seq_assoc_right_def,extract_labels_def,extract_labels_SimpSeq]
    \\ gvs[SUBSET_DEF]
  )
  \\ irule SUBSET_TRANS
  \\ irule_at Any extract_labels_SimpSeq
  \\ fs [Seq_assoc_right_def,extract_labels_def,extract_labels_SimpSeq]
  \\ gvs[SUBSET_DEF]
QED

Theorem extract_labels_remove_unreach[local]:
   set (extract_labels (remove_unreach p)) ⊆ set (extract_labels p)
Proof
  simp[remove_unreach_def]
  \\ irule SUBSET_TRANS
  \\ irule_at (Pos hd) extract_labels_Seq_assoc_right_lemma
  \\ gvs [extract_labels_def]
QED

Theorem MEM_extract_labels_Seq_assoc_right_lemma[local]:
  ∀p1 p2 x.
    MEM x (extract_labels (Seq_assoc_right p1 p2)) ⇒
    MEM x (extract_labels p1) ∨ MEM x (extract_labels p2)
Proof
  rpt strip_tac >>
  assume_tac extract_labels_Seq_assoc_right_lemma >>
  first_x_assum $ qspecl_then [‘p1’,‘p2’] assume_tac>>
  imp_res_tac SUBSET_THM >> fs[]
QED

Theorem helper[local] = MEM_extract_labels_Seq_assoc_right_lemma
                 |> REWRITE_RULE [Once (GSYM CONTRAPOS_THM)]

Theorem ALL_DISTINCT_extract_labels_Seq_assoc_right_lemma[local]:
  ∀p1 p2. ALL_DISTINCT ((extract_labels p1) ++ (extract_labels p2)) ⇒
          ALL_DISTINCT (extract_labels (Seq_assoc_right p1 p2))
Proof
  HO_MATCH_MP_TAC Seq_assoc_right_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_right_def,extract_labels_def,SimpSeq_def] >>
  TRY (CASE_TAC >> fs[extract_labels_def] >> NO_TAC)
  >- (first_x_assum irule >>
      fs[ALL_DISTINCT_APPEND'] >>
      irule_at Any SUBSET_DISJOINT >>
      irule_at Any extract_labels_Seq_assoc_right_lemma >>
      irule_at Any SUBSET_REFL >>
      simp[DISJOINT_UNION'])
  >- (CASE_TAC >> fs[extract_labels_def] >>
      fs [ALL_DISTINCT_APPEND'] >>
      irule_at Any SUBSET_DISJOINT >>
      last_assum $ irule_at Any >>
      irule_at Any SUBSET_TRANS >>
      irule_at Any extract_labels_Seq_assoc_right_lemma >>
      simp[extract_labels_def] >>
      irule_at Any SUBSET_TRANS >>
      irule_at Any extract_labels_Seq_assoc_right_lemma >>
      simp[extract_labels_def] >>
      irule_at Any SUBSET_DISJOINT >>
      irule_at Any extract_labels_Seq_assoc_right_lemma >>
      simp[extract_labels_def] >>
      irule_at Any SUBSET_REFL >> simp[] >>
      irule_at Any SUBSET_DISJOINT >>
      irule_at Any extract_labels_Seq_assoc_right_lemma >>
      simp[extract_labels_def] >>
      irule_at Any SUBSET_REFL >> simp[])
  >- (CASE_TAC >> fs[extract_labels_def] >>
      fs [ALL_DISTINCT_APPEND'] >>
      irule_at Any SUBSET_DISJOINT >>
      last_assum $ irule_at Any >>
      irule_at Any SUBSET_TRANS >>
      irule_at Any extract_labels_Seq_assoc_right_lemma >>
      simp[extract_labels_def])
  >- (rpt (CASE_TAC >> fs[]) >> fs[extract_labels_def]
      >- (irule helper >> simp[extract_labels_def])
      >- (fs[ALL_DISTINCT_APPEND'] >>
          irule_at Any SUBSET_DISJOINT >>
          irule_at Any extract_labels_Seq_assoc_right_lemma >>
          simp[extract_labels_def] >>
          irule_at Any SUBSET_REFL >> simp[] >>
          irule helper >> simp[extract_labels_def])
      >- (fs[ALL_DISTINCT_APPEND'] >>
          irule_at Any SUBSET_DISJOINT >>
          irule_at Any extract_labels_Seq_assoc_right_lemma >>
          irule_at Any extract_labels_Seq_assoc_right_lemma >>
          simp[extract_labels_def] >>
          irule_at Any (iffRL DISJOINT_SYM) >> fs[] >>
          ntac 4 (irule_at Any helper >> simp[extract_labels_def])) >>
      fs[ALL_DISTINCT_APPEND'] >>
      irule_at Any SUBSET_DISJOINT >>
      irule_at Any extract_labels_Seq_assoc_right_lemma >>
      irule_at Any extract_labels_Seq_assoc_right_lemma >>
      simp[extract_labels_def] >>
      irule_at Any (iffRL DISJOINT_SYM) >> fs[] >>
      ntac 4 (irule_at Any helper >> simp[extract_labels_def]) >>
      ntac 2 (irule_at Any SUBSET_DISJOINT >>
              irule_at Any extract_labels_Seq_assoc_right_lemma >>
              simp[extract_labels_def] >>
              irule_at Any SUBSET_REFL >> simp[])) >>
  rpt (CASE_TAC >> fs[]) >> fs[extract_labels_def] >>
  Cases_on ‘p2’ >> fs[dest_Seq_Move_def] >> rename1 ‘Seq p p0’ >>
  Cases_on ‘p’ >> fs[dest_Seq_Move_def,extract_labels_def]
QED

Theorem ALL_DISTINCT_extract_labels_remove_unreach[local]:
   ALL_DISTINCT (extract_labels p) ⇒
   ALL_DISTINCT (extract_labels (remove_unreach p))
Proof
  rw[remove_unreach_def] >>
  irule ALL_DISTINCT_extract_labels_Seq_assoc_right_lemma >>
  simp[extract_labels_def]
QED

Theorem labels_rel_remove_unreach:
  labels_rel (extract_labels q) (extract_labels (remove_unreach q))
Proof
  rw[labels_rel_def]
  >- fs[ALL_DISTINCT_extract_labels_remove_unreach] >>
  irule_at Any extract_labels_remove_unreach>> simp[]
QED

Theorem call_arg_convention_Seq_assoc_right_lemma[local]:
  ∀p1 p2. call_arg_convention p1 ∧ call_arg_convention p2 ⇒
          call_arg_convention (Seq_assoc_right p1 p2)
Proof
  HO_MATCH_MP_TAC Seq_assoc_right_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_right_def,call_arg_convention_def,SimpSeq_def] >>
  TRY (CASE_TAC >> fs[call_arg_convention_def] >> NO_TAC)
  >- (rpt (PURE_CASE_TAC >> fs[]) >> fs[call_arg_convention_def]) >>
  rpt (PURE_CASE_TAC >> fs[]) >> fs[call_arg_convention_def] >>
  Cases_on ‘p2’ >> fs[dest_Seq_Move_def] >> rename1 ‘Seq p p0’ >>
  Cases_on ‘p’ >> fs[dest_Seq_Move_def,call_arg_convention_def]
QED

Theorem call_arg_convention_remove_unreach[local]:
  call_arg_convention p ⇒
  call_arg_convention (remove_unreach p)
Proof
  rw[remove_unreach_def] >>
  irule call_arg_convention_Seq_assoc_right_lemma >>
  simp[call_arg_convention_def]
QED

Theorem every_stack_var_is_stack_var_Seq_assoc_right_lemma[local]:
  ∀p1 p2. every_stack_var is_stack_var p1 ∧
          every_stack_var is_stack_var p2 ⇒
          every_stack_var is_stack_var (Seq_assoc_right p1 p2)
Proof
  HO_MATCH_MP_TAC Seq_assoc_right_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_right_def,
         wordLangTheory.every_stack_var_def,SimpSeq_def] >>
  TRY (CASE_TAC >> fs[wordLangTheory.every_stack_var_def] >> NO_TAC)
  >- (rpt (PURE_CASE_TAC >> fs[]) >>
      fs[wordLangTheory.every_stack_var_def]) >>
  rpt (PURE_CASE_TAC >> fs[]) >> fs[wordLangTheory.every_stack_var_def] >>
  Cases_on ‘p2’ >> fs[dest_Seq_Move_def] >> rename1 ‘Seq p p0’ >>
  Cases_on ‘p’ >> fs[dest_Seq_Move_def,wordLangTheory.every_stack_var_def]
QED

Theorem every_stack_var_is_stack_var_remove_unreach[local]:
  every_stack_var is_stack_var p ⇒
  every_stack_var is_stack_var (remove_unreach p)
Proof
  rw[remove_unreach_def] >>
  irule every_stack_var_is_stack_var_Seq_assoc_right_lemma >>
  simp[wordLangTheory.every_stack_var_def]
QED

Theorem pre_alloc_conventions_remove_unreach:
  pre_alloc_conventions p ⇒
  pre_alloc_conventions (remove_unreach p)
Proof
  rw[pre_alloc_conventions_def]
  >- fs[every_stack_var_is_stack_var_remove_unreach] >>
  simp[call_arg_convention_remove_unreach]
QED

Theorem full_inst_ok_less_Seq_assoc_right_lemma[local]:
  ∀p1 p2. full_inst_ok_less ac p1 ∧ full_inst_ok_less ac p2 ⇒
          full_inst_ok_less ac (Seq_assoc_right p1 p2)
Proof
  HO_MATCH_MP_TAC Seq_assoc_right_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_right_def,full_inst_ok_less_def,SimpSeq_def] >>
  TRY (CASE_TAC >> fs[full_inst_ok_less_def] >> NO_TAC)
  >- (rpt (PURE_CASE_TAC >> fs[]) >> fs[full_inst_ok_less_def]) >>
  rpt (PURE_CASE_TAC >> fs[]) >> fs[full_inst_ok_less_def] >>
  Cases_on ‘p2’ >> fs[dest_Seq_Move_def] >> rename1 ‘Seq p p0’ >>
  Cases_on ‘p’ >> fs[dest_Seq_Move_def,full_inst_ok_less_def]
QED

Theorem full_inst_ok_less_remove_unreach:
  full_inst_ok_less ac p ⇒
  full_inst_ok_less ac (remove_unreach p)
Proof
  rw[remove_unreach_def] >>
  irule full_inst_ok_less_Seq_assoc_right_lemma >>
  simp[full_inst_ok_less_def]
QED

Theorem wf_cutsets_SimpSeq[local]:
  wf_cutsets p1 ∧ wf_cutsets p2 ⇒
  wf_cutsets (SimpSeq p1 p2)
Proof
  rw [SimpSeq_def,wf_cutsets_def]
  \\ Cases_on ‘p1’ \\ rw [wf_cutsets_def]
  \\ Cases_on ‘dest_Seq_Move p2’ \\ gvs []
  \\ rw [wf_cutsets_def] \\ gvs [SUBSET_DEF]
  \\ PairCases_on ‘x’ \\ gvs []
  \\ pop_assum mp_tac \\ rw []
  \\ gvs [oneline dest_Seq_Move_def, AllCaseEqs(), wf_cutsets_def]
QED

Theorem wf_cutsets_Seq_assoc_right_lemma[local]:
  ∀p1 p2.
  wf_cutsets p1 ∧ wf_cutsets p2 ⇒
  wf_cutsets (Seq_assoc_right p1 p2)
Proof
  HO_MATCH_MP_TAC Seq_assoc_right_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_right_def,wf_cutsets_def]
  >~ [`Call`]
  >- (
    every_case_tac \\ gvs[wf_cutsets_def]
    \\ match_mp_tac wf_cutsets_SimpSeq
    \\ gvs[wf_cutsets_def])
  \\ match_mp_tac wf_cutsets_SimpSeq
  \\ gvs[wf_cutsets_def]
QED

Theorem wf_cutsets_remove_unreach:
  wf_cutsets p ⇒ wf_cutsets (remove_unreach p)
Proof
  rw[remove_unreach_def]
  \\ irule wf_cutsets_Seq_assoc_right_lemma
  \\ gvs[wf_cutsets_def]
QED

Theorem every_inst_SimpSeq[local]:
  every_inst P p1 ∧ every_inst P p2 ⇒
  every_inst P (SimpSeq p1 p2)
Proof
  rw [SimpSeq_def,every_inst_def]
  \\ Cases_on ‘p1’ \\ rw [every_inst_def]
  \\ Cases_on ‘dest_Seq_Move p2’ \\ gvs []
  \\ rw [every_inst_def] \\ gvs [SUBSET_DEF]
  \\ PairCases_on ‘x’ \\ gvs []
  \\ pop_assum mp_tac \\ rw []
  \\ gvs [oneline dest_Seq_Move_def, AllCaseEqs(), every_inst_def]
QED

Theorem every_inst_Seq_assoc_right_lemma[local]:
  ∀p1 p2.
  every_inst P p1 ∧ every_inst P p2 ⇒
  every_inst P (Seq_assoc_right p1 p2)
Proof
  HO_MATCH_MP_TAC Seq_assoc_right_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_right_def,every_inst_def]
  >~ [`Call`]
  >- (
    every_case_tac \\ gvs[every_inst_def]
    \\ match_mp_tac every_inst_SimpSeq
    \\ gvs[every_inst_def])
  \\ match_mp_tac every_inst_SimpSeq
  \\ gvs[every_inst_def]
QED

Theorem every_inst_remove_unreach:
  every_inst P p ⇒
  every_inst P (remove_unreach p)
Proof
  rw[remove_unreach_def]
  \\ irule every_inst_Seq_assoc_right_lemma
  \\ gvs[every_inst_def]
QED

Theorem flat_exp_conventions_SimpSeq[local]:
  flat_exp_conventions p1 ∧ flat_exp_conventions p2 ⇒
  flat_exp_conventions (SimpSeq p1 p2)
Proof
  rw [SimpSeq_def,flat_exp_conventions_def]
  \\ Cases_on ‘p1’ \\ rw [flat_exp_conventions_def]
  \\ Cases_on ‘dest_Seq_Move p2’ \\ gvs []
  \\ rw [flat_exp_conventions_def] \\ gvs [SUBSET_DEF]
  \\ PairCases_on ‘x’ \\ gvs []
  \\ pop_assum mp_tac \\ rw []
  \\ gvs [oneline dest_Seq_Move_def, AllCaseEqs(), flat_exp_conventions_def]
QED

Theorem flat_exp_conventions_Seq_assoc_right_lemma[local]:
  ∀p1 p2.
  flat_exp_conventions p1 ∧ flat_exp_conventions p2 ⇒
  flat_exp_conventions (Seq_assoc_right p1 p2)
Proof
  HO_MATCH_MP_TAC Seq_assoc_right_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_right_def,flat_exp_conventions_def]
  >~ [`Call`]
  >- (
    every_case_tac \\ gvs[flat_exp_conventions_def]
    \\ match_mp_tac flat_exp_conventions_SimpSeq
    \\ gvs[flat_exp_conventions_def])
  \\ match_mp_tac flat_exp_conventions_SimpSeq
  \\ gvs[flat_exp_conventions_def]
QED

Theorem flat_exp_conventions_remove_unreach:
  flat_exp_conventions p ⇒
  flat_exp_conventions (remove_unreach p)
Proof
  rw[remove_unreach_def]
  \\ irule flat_exp_conventions_Seq_assoc_right_lemma
  \\ gvs[flat_exp_conventions_def]
QED

(*** word_alloc ***)
Theorem apply_colour_lab_pres[local]:
  ∀col prog.
  extract_labels prog = extract_labels (apply_colour col prog)
Proof
  ho_match_mp_tac apply_colour_ind>>
  fs[extract_labels_def]>>rw[]>>
  EVERY_CASE_TAC>>fs[]
QED

Theorem word_alloc_lab_pres:
  extract_labels prog = extract_labels (word_alloc fc c alg k prog col_opt)
Proof
  fs[word_alloc_def,oracle_colour_ok_def]>>
  EVERY_CASE_TAC>>fs[]>>
  TRY(pairarg_tac)>>fs[]>>
  EVERY_CASE_TAC>>fs[]>>
  metis_tac[apply_colour_lab_pres]
QED

Theorem word_alloc_flat_exp_conventions_lem[local]:
  ∀f prog.
  flat_exp_conventions prog ⇒
  flat_exp_conventions (apply_colour f prog)
Proof
  ho_match_mp_tac apply_colour_ind>>full_simp_tac(srw_ss())[flat_exp_conventions_def]>>srw_tac[][]
  >-
    (EVERY_CASE_TAC>>unabbrev_all_tac>>full_simp_tac(srw_ss())[flat_exp_conventions_def])
  >-
    (Cases_on`exp`>>full_simp_tac(srw_ss())[flat_exp_conventions_def])
  >>
    gvs[DefnBase.one_line_ify NONE flat_exp_conventions_def] >>
    first_x_assum mp_tac >>
    rpt (TOP_CASE_TAC >> simp[])
QED

Theorem word_alloc_flat_exp_conventions:
  ∀fc c alg k prog col_opt.
  flat_exp_conventions prog ⇒
  flat_exp_conventions (word_alloc fc c alg k prog col_opt)
Proof
  full_simp_tac(srw_ss())[word_alloc_def,oracle_colour_ok_def]>>
  srw_tac[][]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[LET_THM]>>
  metis_tac[word_alloc_flat_exp_conventions_lem]
QED

Theorem word_alloc_two_reg_inst_lem[local]:
  ∀f prog.
  every_inst two_reg_inst prog ⇒
  every_inst two_reg_inst (apply_colour f prog)
Proof
  ho_match_mp_tac apply_colour_ind>>
  fs[every_inst_def]>>rw[]
  >-
    (Cases_on`i`>>TRY(Cases_on`a`)>>TRY(Cases_on`m`)>>TRY(Cases_on`f'`)>>
    fs[apply_colour_inst_def,two_reg_inst_def])
  >>
    EVERY_CASE_TAC>>unabbrev_all_tac>>
    fs[every_inst_def,apply_colour_inst_def,two_reg_inst_def]
QED

Theorem word_alloc_two_reg_inst:
  ∀fc c alg k prog col_opt.
  every_inst two_reg_inst prog ⇒
  every_inst two_reg_inst (word_alloc fc c alg k prog col_opt)
Proof
  fs[word_alloc_def,oracle_colour_ok_def]>>
  rw[]>>
  EVERY_CASE_TAC>>
  rpt (pairarg_tac>>fs[])>>
  EVERY_CASE_TAC>>fs[]>>
  metis_tac[word_alloc_two_reg_inst_lem]
QED

Theorem apply_colour_not_created_subprogs[local]:
  not_created_subprogs P prog ⇒
  not_created_subprogs P (apply_colour f prog)
Proof
  qid_spec_tac ‘prog’>>qid_spec_tac ‘f’>>
  recInduct word_allocTheory.apply_colour_ind>>
  rw[word_allocTheory.apply_colour_def,
     not_created_subprogs_def]>>gs[]>>
  every_case_tac>>gs[]
QED

Theorem word_alloc_not_created_subprogs[local]:
  not_created_subprogs P prog ⇒
  not_created_subprogs P (word_alloc n c a r prog cl)
Proof
  rw[word_allocTheory.word_alloc_def]>>
  every_case_tac>>gs[not_created_subprogs_def]
  >- (pairarg_tac>>gs[]>>
      every_case_tac>>gs[not_created_subprogs_def]>>
      irule apply_colour_not_created_subprogs>>rw[])>>
  gs[word_allocTheory.oracle_colour_ok_def]>>
  every_case_tac>>gs[not_created_subprogs_def]>>
  rveq>>irule apply_colour_not_created_subprogs>>rw[]
QED

Theorem word_get_code_labels_apply_colour[local]:
  ∀col ps.
  word_get_code_labels (apply_colour col ps) =
  word_get_code_labels ps
Proof
  ho_match_mp_tac apply_colour_ind>>rw[]>>
  fs[apply_colour_def]>>
  every_case_tac>>fs[]
QED

Theorem word_good_handlers_apply_colour[local]:
  ∀col ps.
  word_good_handlers n (apply_colour col ps) ⇔
  word_good_handlers n ps
Proof
  ho_match_mp_tac apply_colour_ind>>rw[]>>
  fs[apply_colour_def]>>
  every_case_tac>>fs[]
QED

Theorem word_get_code_labels_word_alloc[local]:
  word_get_code_labels (word_alloc fc c alg k prog col_opt) =
  word_get_code_labels prog
Proof
  fs[word_alloc_def,oracle_colour_ok_def]>>
  EVERY_CASE_TAC>>fs[]>>
  TRY(pairarg_tac)>>fs[]>>
  EVERY_CASE_TAC>>fs[]>>
  metis_tac[word_get_code_labels_apply_colour]
QED

Theorem word_good_handlers_word_alloc[local]:
  word_good_handlers n (word_alloc fc c alg k prog col_opt) ⇔
  word_good_handlers n prog
Proof
  fs[word_alloc_def,oracle_colour_ok_def]>>
  EVERY_CASE_TAC>>fs[]>>
  TRY(pairarg_tac)>>fs[]>>
  EVERY_CASE_TAC>>fs[]>>
  metis_tac[word_good_handlers_apply_colour]
QED

(*** remove_must_terminate ***)

val rmt_convs = [flat_exp_conventions_def, full_inst_ok_less_def,
  every_inst_def, post_alloc_conventions_def, call_arg_convention_def,
  wordLangTheory.every_stack_var_def, wordLangTheory.every_var_def,
  extract_labels_def]

Theorem remove_must_terminate_conventions:
  ∀p c k.
  let comp = remove_must_terminate p in
  (flat_exp_conventions p ⇒ flat_exp_conventions comp) ∧
  (full_inst_ok_less c p ⇒ full_inst_ok_less c comp) ∧
  (post_alloc_conventions k p ⇒ post_alloc_conventions k comp) ∧
  (every_inst P p ⇒ every_inst P comp) ∧
  (extract_labels p = extract_labels comp)
Proof
  ho_match_mp_tac remove_must_terminate_ind>>rw[]>>
  fs[remove_must_terminate_def]>>fs rmt_convs>>
  TRY
  (rename1`args = A`>>
  Cases_on`ret`>>fs[]>>
  PairCases_on`x`>>fs[]>>
  Cases_on`h`>>fs[]>- metis_tac[]>>
  PairCases_on`x`>>fs[]>>
  metis_tac[])>>
  EVERY_CASE_TAC>>fs[]>>
  metis_tac[]
QED

Theorem word_get_code_labels_remove_must_terminate[local]:
  ∀ps.
  word_get_code_labels (remove_must_terminate ps) =
  word_get_code_labels ps
Proof
  ho_match_mp_tac remove_must_terminate_ind>>rw[]>>
  fs[remove_must_terminate_def]>>
  every_case_tac>>fs[]
QED

Theorem word_good_handlers_remove_must_terminate[local]:
  ∀ps.
  word_good_handlers n (remove_must_terminate ps) ⇔
  word_good_handlers n ps
Proof
  ho_match_mp_tac remove_must_terminate_ind>>rw[]>>
  fs[remove_must_terminate_def]>>
  every_case_tac>>fs[]
QED

(*** word_to_word ***)
Theorem compile_single_not_created_subprogs:
  not_created_subprogs P (SND (SND (FST prog_opt))) ==>
  not_created_subprogs P (SND (SND
    (compile_single two_reg_arith reg_count alg c prog_opt)))
Proof
  PairCases_on `prog_opt`>>
  strip_tac>>
  fs[word_to_wordTheory.compile_single_def]>>
  irule word_alloc_not_created_subprogs>>
  irule remove_dead_prog_not_created_subprogs>>
  irule remove_unreach_not_created_subprogs>>
  irule three_to_two_reg_prog_not_created_subprogs>>
  irule copy_prop_not_created_subprogs>>
  irule word_common_subexp_elim_not_created_subprogs>>
  irule remove_dead_prog_not_created_subprogs>>
  irule full_ssa_cc_trans_not_created_subprogs>>
  irule inst_select_not_created_subprogs>>
  irule compile_exp_not_created_subprogs>>rw[]
QED

Theorem word_good_handlers_word_to_word_incr_helper[local]:
  ∀oracles.
  LENGTH progs = LENGTH oracles ⇒
  EVERY (λ(n,m,pp). word_good_handlers n pp) progs ⇒
  EVERY (λ(n,m,pp). word_good_handlers n pp)
  (MAP (full_compile_single tra reg_count1
        ralg asm_c) (ZIP (progs,oracles)))
Proof
  rw[]>>
  rfs[EVERY_MAP,LENGTH_GENLIST,EVERY_MEM,MEM_ZIP,PULL_EXISTS]>>
  rw[full_compile_single_def]>>
  Cases_on`EL n progs`>>Cases_on`r`>>
  fs[compile_single_def]>>
  fs[word_good_handlers_remove_must_terminate,word_good_handlers_word_alloc]>>
  simp[word_good_handlers_remove_dead_prog]>>
  match_mp_tac word_good_handlers_remove_unreach>>
  simp[word_good_handlers_three_to_two_reg_prog]>>
  simp[word_good_handlers_copy_prop,word_good_handlers_word_common_subexp_elim,word_good_handlers_remove_dead_prog,word_good_handlers_full_ssa_cc_trans,word_good_handlers_inst_select]>>
  match_mp_tac word_good_handlers_word_simp>>
  fs[FORALL_PROD]>>
  metis_tac[EL_MEM]
QED

Theorem word_good_handlers_word_to_word_incr:
  EVERY (λ(n,m,pp). word_good_handlers n pp) progs ⇒
  EVERY (λ(n,m,pp). word_good_handlers n pp)
    (MAP (\p. full_compile_single tra reg_count1 ralg asm_c (p, NONE)) progs)
Proof
  strip_tac>>
  qspec_then `MAP (\p. NONE) progs` assume_tac word_good_handlers_word_to_word_incr_helper>>
  fs[ZIP_MAP,MAP_MAP_o,o_DEF]
QED

Theorem word_good_handlers_word_to_word:
  EVERY (λ(n,m,pp). word_good_handlers n pp) progs ⇒
  EVERY (λ(n,m,pp). word_good_handlers n pp) (SND (compile wc ac progs))
Proof
  fs[word_to_wordTheory.compile_def]>>
  rpt(pairarg_tac>>fs[])>>
  match_mp_tac word_good_handlers_word_to_word_incr_helper >>
  fs[next_n_oracle_def]>>
  every_case_tac>>fs[]>>
  rveq>>fs[]
QED

Theorem word_good_code_labels_word_to_word_incr_helper[local]:
  ∀oracles.
  LENGTH progs = LENGTH oracles ⇒
  word_good_code_labels progs elabs ⇒
  word_good_code_labels
  (MAP (full_compile_single tra reg_count1
        ralg asm_c) (ZIP (progs,oracles))) elabs
Proof
  fs[wordConvsTheory.good_code_labels_def]>>
  rw[]
  >-
    metis_tac[word_good_handlers_word_to_word_incr_helper]
  >>
    fs[SUBSET_DEF,PULL_EXISTS,MEM_MAP,MEM_ZIP]>>
    rw[full_compile_single_def]>>
    rpt(pairarg_tac>>gvs[])>>
    Cases_on`EL n progs`>>Cases_on`r`>>
    gvs[compile_single_def]>>
    fs[word_get_code_labels_remove_must_terminate,word_get_code_labels_word_alloc]>>
    dxrule (word_get_code_labels_remove_dead_prog|>SIMP_RULE std_ss [SUBSET_DEF])>>
    strip_tac>>
    dxrule (word_get_code_labels_remove_unreach|>SIMP_RULE std_ss [SUBSET_DEF])>>
    simp[
      word_get_code_labels_three_to_two_reg_prog,
      word_get_code_labels_copy_prop,
      word_get_code_labels_word_common_subexp_elim]>>
    strip_tac>>
    dxrule (word_get_code_labels_remove_dead_prog|>SIMP_RULE std_ss [SUBSET_DEF])>>
    simp[word_get_code_labels_full_ssa_cc_trans,word_get_code_labels_inst_select]>>
    strip_tac>>
    dxrule (word_get_code_labels_word_simp|>SIMP_RULE std_ss [SUBSET_DEF])>>
    fs[FORALL_PROD,EXISTS_PROD,PULL_EXISTS,EVERY_MEM]>>
    strip_tac>>
    first_x_assum drule>>
    simp[MEM_EL,PULL_EXISTS]>>
    strip_tac>>first_x_assum (drule_at Any)>>
    simp[]>>rw[]
    >- (
      rename1`nn < LENGTH _`>>
      DISJ1_TAC>>
      qexists_tac`nn`>>simp[]>>
      Cases_on`EL nn progs`>>Cases_on`r`>>
      fs[compile_single_def])>>
    simp[]
QED

(* The actual incremental theorem to use in the backend *)
Theorem word_good_code_labels_word_to_word_incr:
  word_good_code_labels progs elabs ⇒
  word_good_code_labels
    (MAP (\p. full_compile_single tra reg_count1 ralg asm_c (p, NONE)) progs) elabs
Proof
  strip_tac>>
  qspec_then `MAP (\p. NONE) progs` assume_tac word_good_code_labels_word_to_word_incr_helper>>
  fs[ZIP_MAP,MAP_MAP_o,o_DEF]
QED

Theorem word_good_code_labels_word_to_word:
  word_good_code_labels progs elabs ⇒
  word_good_code_labels (SND (compile wc ac progs)) elabs
Proof
  fs[word_to_wordTheory.compile_def]>>
  rpt(pairarg_tac>>fs[])>>
  match_mp_tac word_good_code_labels_word_to_word_incr_helper>>
  fs[next_n_oracle_def]>>
  every_case_tac>>fs[]>>
  rveq>>fs[]
QED

