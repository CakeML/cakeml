(*
  Syntactic properties proofs for word_to_word.
*)
open preamble wordLangTheory word_to_wordTheory wordConvsTheory
  word_simpTheory word_allocTheory word_instTheory word_unreachTheory
  word_removeTheory word_cseTheory word_elimTheory word_copyTheory;

val _ = new_theory "wordConvsProof";

(***
  This theory should serve also as documentation for
  the syntactic properties of wordLang that gets preserved
  across passes.
  It must NOT depend on the semantics or word_Xproof files.

  OVERVIEW (TO BE FILLED):

  word_simp$compile_exp
  ===
    1 preserves label_rel: extract_labels_compile_exp
    2 preserves every_inst: compile_exp_no_inst
    3 preserves subprogs: compile_exp_not_created_subprogs
    4 TODO

  inst_select
  ===
    1 preserves label_rel: inst_select_lab_pres (equality on labels)
    3 preserves subprogs: inst_select_not_created_subprogs

    creates flat_exp_conventions: inst_select_flat_exp_conventions
    creates full_inst_ok_less: inst_select_full_inst_ok_less
    TODO

  full_ssa_cc_trans
  ===
    TODO

  remove_dead_prog (note this is ran again after remove_unreach)
  ===
    1 preserves label_rel: remove_dead_prog_conventions (equality on labels)
    preserves flat_exp_conventions: remove_dead_prog_conventions
    preserves full_inst_ok_less: remove_dead_prog_conventions
    preserves pre_alloc_conventions: remove_dead_prog_conventions
    preserves every_inst: remove_dead_prog_conventions
    preserves wf_cutsets: remove_dead_prog_conventions

  word_common_subexp_elim
  ===
    TODO

  copy_prop
  ===
    TODO

  three_to_two_reg_prog
  ===
    1 preserves label_rel: three_to_two_reg_prog_lab_pres (equality on labels)

    3 preserves subprogs: three_to_two_reg_prog_not_created_subprogs
    creates two_reg_inst: three_to_two_reg_prog_two_reg_inst (under a flag)

    preserves wf_cutsets: three_to_two_reg_prog_wf_cutsets

    preserves pre_alloc_conventions: three_to_two_reg_prog_pre_alloc_conventions
    preserves flat_exp_conventions: three_to_two_reg_prog_flat_exp_conventions
    TODO


  remove_unreach
  ===
    TODO

  word_to_word (overall)
  ===
    TODO
***)

(*** word_simp$compile_exp ***)

(* labels_rel *)
Theorem extract_labels_SmartSeq:
   extract_labels (SmartSeq p1 p2) = extract_labels (Seq p1 p2)
Proof
  rw [SmartSeq_def,extract_labels_def]
QED

Theorem extract_labels_Seq_assoc_lemma:
   !p1 p2. extract_labels (Seq_assoc p1 p2) =
            extract_labels p1 ++ extract_labels p2
Proof
  HO_MATCH_MP_TAC Seq_assoc_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_def,extract_labels_def,extract_labels_SmartSeq]
  \\ Cases_on `ret_prog` \\ Cases_on `handler` \\ fs []
  \\ PairCases_on `x` \\ fs []
  \\ PairCases_on `x'` \\ fs []
QED

Theorem extract_labels_Seq_assoc:
   extract_labels (Seq_assoc Skip p) = extract_labels p
Proof
  fs [extract_labels_Seq_assoc_lemma,extract_labels_def]
QED

Triviality extract_labels_drop_consts_1:
  extract_labels (drop_consts cs ls) = []
Proof
  Induct_on`ls`>>rw[drop_consts_def]>>
  every_case_tac>>
  rw[extract_labels_SmartSeq,extract_labels_def]
QED

Triviality extract_labels_drop_consts[simp]:
  extract_labels (SmartSeq (drop_consts cs ls) p) = extract_labels p
Proof
  rw[extract_labels_SmartSeq,extract_labels_def,extract_labels_drop_consts_1]
QED

Triviality extract_labels_const_fp_loop:
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

Theorem extract_labels_const_fp:
   labels_rel (extract_labels p) (extract_labels (const_fp p))
Proof
  fs [const_fp_def] \\ Cases_on `const_fp_loop p LN`
  \\ drule extract_labels_const_fp_loop
  \\ simp []
QED

Triviality labels_rel_append_imp:
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

Triviality const_fp_loop_Seq =
  const_fp_loop_def |> BODY_CONJUNCTS
  |> filter (can (find_term (fn t => total (fst o dest_const) t = SOME "Seq")) o concl)
  |> LIST_CONJ

(* The tricky part: to prove this syntactic property (and only for this) we
   have to show that the strategy actually works, and that any program which
   the hoist mechanism hoists will simplify (via const_fp) back to a program
   in which nothing is duplicated. *)
Triviality const_fp_loop_dummy_cases:
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

Theorem dest_If_thm:
   dest_If x2 = SOME (g1,g2,g3,g4,g5) <=> x2 = If g1 g2 g3 g4 g5
Proof
  Cases_on `x2` \\ fs [dest_If_def]
QED

Triviality labels_rel_hoist2:
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

Theorem labels_rel_simp_duplicate_if:
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

Theorem extract_labels_compile_exp:
  !p. labels_rel (extract_labels p)
                 (extract_labels (word_simp$compile_exp p))
Proof
  rw [word_simpTheory.compile_exp_def] >>
  irule labels_rel_TRANS >> ONCE_REWRITE_TAC [CONJ_COMM] >>
  irule_at Any labels_rel_simp_duplicate_if >>
  irule labels_rel_TRANS >> ONCE_REWRITE_TAC [CONJ_COMM] >>
  irule_at Any extract_labels_const_fp >>
  simp [extract_labels_Seq_assoc]
QED

(* inst_ok_less *)
Triviality dest_Seq_no_inst:
  ∀prog.
  every_inst P prog ⇒
  every_inst P (FST (dest_Seq prog)) ∧
  every_inst P (SND (dest_Seq prog))
Proof
  ho_match_mp_tac dest_Seq_ind>>rw[dest_Seq_def]>>fs[every_inst_def]
QED

Triviality Seq_assoc_no_inst:
  ∀p1 p2.
  every_inst P p1 ∧ every_inst P p2 ⇒
  every_inst P (Seq_assoc p1 p2)
Proof
  ho_match_mp_tac Seq_assoc_ind>>
  fs[Seq_assoc_def,SmartSeq_def]>>rw[]>>
  fs[every_inst_def]>>
  every_case_tac>>fs[]
QED

Triviality every_inst_SmartSeq:
  every_inst P (SmartSeq p q) =
  (every_inst P p ∧ every_inst P q)
Proof
  rw[SmartSeq_def,every_inst_def]
QED

Triviality every_inst_inst_ok_less_drop_consts[simp]:
  every_inst P (SmartSeq (drop_consts cs ls) p) =
  every_inst P p
Proof
  rw[every_inst_SmartSeq]>>
  `every_inst P (drop_consts cs ls)` by (
    Induct_on`ls`>>rw[drop_consts_def]>>every_case_tac>>
    rw[every_inst_def,every_inst_SmartSeq] )>>
  rw[]
QED

Theorem every_inst_inst_ok_less_const_fp:
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

Triviality try_if_hoist2_no_inst:
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
  \\ fs [every_inst_def, every_inst_inst_ok_less_const_fp]
QED

Triviality simp_duplicate_if_no_inst:
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
  \\ fs [every_inst_def, Seq_assoc_no_inst, every_inst_inst_ok_less_const_fp]
QED

Theorem compile_exp_no_inst:
  ∀prog.
    every_inst P prog ⇒
    every_inst P (compile_exp prog)
Proof
  fs[compile_exp_def]>>
  metis_tac[Seq_assoc_no_inst,every_inst_def,
            every_inst_inst_ok_less_const_fp,simp_duplicate_if_no_inst]
QED

Triviality not_created_subprogs_SmartSeq:
   not_created_subprogs P (SmartSeq p1 p2) =
   (not_created_subprogs P p1 /\ not_created_subprogs P p2)
Proof
  rw [SmartSeq_def,not_created_subprogs_def]
QED

Theorem not_created_subprogs_Seq_assoc:
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


Triviality not_created_subprogs_drop_consts[simp]:
  not_created_subprogs P (SmartSeq (drop_consts cs ls) p) =
  not_created_subprogs P p
Proof
  rw[not_created_subprogs_SmartSeq]>>
  `not_created_subprogs P (drop_consts cs ls)` by (
    Induct_on`ls`>>rw[drop_consts_def]>>every_case_tac>>
    rw[not_created_subprogs_def,not_created_subprogs_SmartSeq])>>
  rw[]
QED

Triviality not_created_subprogs_const_fp_loop:
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

Theorem not_created_subprogs_const_fp:
  not_created_subprogs P p ==>
  not_created_subprogs P (const_fp p)
Proof
  rw [const_fp_def]
  \\ Cases_on `const_fp_loop p LN` \\ fs []
  \\ imp_res_tac not_created_subprogs_const_fp_loop
QED

Triviality not_created_subprogs_hoist2:
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

Triviality not_created_subprogs_simp_duplicate_if:
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

Theorem compile_exp_not_created_subprogs:
  not_created_subprogs P p ==>
  not_created_subprogs P (compile_exp p)
Proof
  rw [compile_exp_def, not_created_subprogs_const_fp,
    not_created_subprogs_simp_duplicate_if, not_created_subprogs_Seq_assoc,
    not_created_subprogs_def]
QED

(*** inst_select ***)

(* label preservation stuff *)
Triviality inst_select_exp_no_lab:
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
Triviality inst_select_exp_flat_exp_conventions:
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

Theorem inst_select_exp_not_created_subprogs:
  not_created_subprogs P (inst_select_exp c c' n exp)
Proof
  MAP_EVERY qid_spec_tac [‘exp’, ‘n’, ‘c'’, ‘c’]>>
  ho_match_mp_tac word_instTheory.inst_select_exp_ind>>
  rw[word_instTheory.inst_select_exp_def, not_created_subprogs_def]>>
  every_case_tac>>
  gs[not_created_subprogs_def, word_instTheory.inst_select_exp_def]
QED

Theorem inst_select_not_created_subprogs:
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
Triviality inst_select_exp_full_inst_ok_less:
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

(*** remove_dead_prog ***)
val convs = [flat_exp_conventions_def,full_inst_ok_less_def,every_inst_def,pre_alloc_conventions_def,call_arg_convention_def,every_stack_var_def,every_var_def,extract_labels_def,wf_cutsets_def];

Theorem remove_dead_conventions:
  ∀p live c k.
    let comp = FST (remove_dead p live) in
    (flat_exp_conventions p ⇒ flat_exp_conventions comp) ∧
    (full_inst_ok_less c p ⇒ full_inst_ok_less c comp) ∧
    (pre_alloc_conventions p ⇒
      pre_alloc_conventions comp) ∧
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
  (remove_dead_conventions |> Q.SPEC`p` |> Q.SPEC`LN` |> SPEC_ALL |>
    SIMP_RULE std_ss [LET_THM,FORALL_AND_THM,GSYM remove_dead_prog_def]);

(*** three_to_to_reg_prog ***)
Theorem three_to_two_reg_prog_lab_pres:
  ∀prog.
  extract_labels prog = extract_labels (three_to_two_reg_prog b prog)
Proof
  simp[three_to_two_reg_prog_def]>>
  ho_match_mp_tac three_to_two_reg_ind>>
  rw[three_to_two_reg_def,extract_labels_def]>>EVERY_CASE_TAC>>fs[]
QED

Theorem three_to_two_reg_prog_not_created_subprogs:
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
(*
Theorem three_to_two_reg_flat_exp_conventions:
  ∀prog. flat_exp_conventions prog ⇒ flat_exp_conventions (three_to_two_reg prog)
Proof
  ho_match_mp_tac three_to_two_reg_ind>>srw_tac[][]>>
  full_simp_tac(srw_ss())[flat_exp_conventions_def,three_to_two_reg_def,LET_THM]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]
QED
*)
Theorem three_to_two_reg_full_inst_ok_less:
  ∀prog. full_inst_ok_less c prog ⇒
         full_inst_ok_less c (three_to_two_reg prog)
Proof
  ho_match_mp_tac three_to_two_reg_ind>>srw_tac[][]>>
  full_simp_tac(srw_ss())[three_to_two_reg_def,LET_THM]>>EVERY_CASE_TAC>>fs[full_inst_ok_less_def]
  >-
    (Cases_on`bop`>>Cases_on`ri`>>fs[full_inst_ok_less_def,inst_ok_less_def,every_inst_def])
  >-
    (Cases_on`n`>>fs[inst_ok_less_def])
  >>
    metis_tac[inst_ok_less_def]
QED
val _ = export_theory();
