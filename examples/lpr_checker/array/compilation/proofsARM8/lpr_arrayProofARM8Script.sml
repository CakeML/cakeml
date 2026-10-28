(*
  Compose the semantics theorem and the compiler correctness
  theorem with the compiler evaluation theorem to produce end-to-end
  correctness theorem that reaches final machine code.
*)
Theory lpr_arrayProofARM8
Ancestors
  semanticsProps backendProof arm8_asl_configProof TextIOProof
  fsFFIProps satSem lpr lpr_list lpr_arrayFullProg lpr_parsing
  lpr_arrayCompileARM8 lpr_composeProg
Libs
  preamble

val check_unsat_terminate = UNDISCH_ALL check_unsat_semantics
  |> SIMP_RULE bool_ss [RIGHT_EXISTS_AND_THM]
  |> HO_MATCH_MP ml_progTheory.sem_satisfies_IMP_Terminate
  |> SRULE [lpr_array_compiled];

Theorem check_unsat_compiled_thm =
  MATCH_MP compile_correct (cj 1 lpr_array_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP (cj 1 check_unsat_terminate)
  |> C MATCH_MP arm8_configProofTheory.arm8_backend_config_ok
  |> Q.GEN ‘mc’ |> ISPEC (arm8_asl_init_ok |> concl |> rand |> rand) |> UNDISCH_ALL
  |> MATCH_MP (cj 2 check_unsat_terminate)
  |> REWRITE_RULE [targetPropsTheory.machine_sem_sing] |> DISCH_ALL
  |> CONJ (CONJ (UNDISCH arm8_asl_machine_config_ok) (UNDISCH arm8_asl_init_ok))
  |> SRULE [SF CONJ_ss] |> CONJUNCT2 |> DISCH_ALL
  |> REWRITE_RULE [AND_IMP_INTRO, GSYM CONJ_ASSOC]
  |> check_thm

(* Prettifying the standard parts of all the theorems *)
Definition installed_arm8_asl_def:
  installed_arm8_asl ((code, data, cfg) :
      (word8 list # num list # backend$config))
    mc ms
  <=>
    ?cbspace data_sp.
      is_arm8_asl_machine_config mc /\
      installed
        code cbspace
        data data_sp
        cfg.lab_conf.ffi_names
        (heap_regs arm8_backend_config.stack_conf.reg_names) mc
        cfg.lab_conf.shmem_extra ms
End

Definition check_unsat_code_def:
  check_unsat_code = (code, data, info)
End

(* A standard run of cake_lpr satisfying all the default assumptions *)
Definition cake_lpr_run_def:
  cake_lpr_run cl fs mc ms ⇔
  wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ∧
  installed_arm8_asl check_unsat_code mc ms
End

Theorem concat_success_str:
  ∀a b c. concat [«s VERIFIED INTERVALS COVER 0-»; toString (d:num); «\n»] ≠ success_str a b c
Proof
  rw[]>>
  simp[success_str_def,expected_prefix_def]>>
  simp[mlstringTheory.concat_def]>>
  qmatch_goalsub_abbrev_tac`STRING #"I" (STRING #"N" lss)`>>
  qmatch_goalsub_abbrev_tac`STRING #"R" (STRING #"A" lsss)`>>
  EVAL_TAC
QED

Theorem check_lines_success_str:
  check_lines a b c d = INR y ⇒
  y = concat [«s VERIFIED INTERVALS COVER 0-»; toString d; «\n»] ∧
  ∀a b c. y ≠ success_str a b c
Proof
  simp[check_lines_def]>>
  every_case_tac>>rw[]>>
  metis_tac[concat_success_str]
QED

Theorem TL_eq_hd_exists:
  TL cl = ls ⇒
  (ls ≠ [] ⇒ ∃x. cl = x :: ls)
Proof
  Cases_on`cl`>>rw[]
QED

Theorem machine_code_sound:
  cake_lpr_run cl fs mc ms ⇒
  ∃io.
  machine_sem mc (basis_ffi ext cl fs) ms ⊆
    extend_with_resource_limit {Terminate Success io} ∧
  ∃out err.
    extract_fs ext (cl,fs) io =
      SOME (add_stdout (add_stderr fs err) out) ∧
  (out ≠ «» ⇒
  if LENGTH cl = 2 then
    inFS_fname fs (EL 1 cl) ∧
    ∃fml.
      parse_dimacs (all_lines_file fs (EL 1 cl)) = SOME fml ∧
      out = concat (print_dimacs fml)
  else if LENGTH cl = 3 then
    inFS_fname fs (EL 1 cl) ∧
    ∃fml.
      parse_dimacs (all_lines_file fs (EL 1 cl)) = SOME fml ∧
      out = «s VERIFIED UNSAT\n» ∧
      unsatisfiable (interp fml)
  else if LENGTH cl = 4 then
    inFS_fname fs (EL 1 cl) ∧ inFS_fname fs (EL 3 cl) ∧
    ∃fml fml2.
      parse_dimacs (all_lines_file fs (EL 1 cl)) = SOME fml ∧
      parse_dimacs (all_lines_file fs (EL 3 cl)) = SOME fml2 ∧
      out = «s VERIFIED TRANSFORMATION\n» ∧
      (satisfiable (interp fml) ⇒ satisfiable (interp fml2))
  else if LENGTH cl = 5 then
    case parse_rng_or_check (EL 3 cl) of NONE => F
    | SOME (INL()) =>
        inFS_fname fs (EL 1 cl) ∧
        inFS_fname fs (EL 2 cl) ∧
        inFS_fname fs (EL 4 cl) ∧
        check_lines
          (implode (md5 (THE (file_content fs (EL 1 cl)))))
          (implode (md5 (THE (file_content fs (EL 2 cl)))))
          (all_lines_file fs (EL 4 cl))
          (LENGTH (all_lines_file fs (EL 2 cl))) = INR out ∧
          ∃n:num.
            out = concat [«s VERIFIED INTERVALS COVER 0-»; toString n; «\n»]
    | SOME (INR (i,j)) =>
      inFS_fname fs (EL 1 cl) ∧ inFS_fname fs (EL 2 cl) ∧
      ∃fml pf.
        out = success_str
          (implode (md5 (THE (file_content fs (EL 1 cl)))))
          (implode (md5 (THE (file_content fs (EL 2 cl)))))
          (print_rng i j) ∧
        parse_dimacs (all_lines_file fs (EL 1 cl)) = SOME fml ∧
        parse_proof (all_lines_file fs (EL 2 cl)) = SOME pf ∧
        i ≤ j ∧ j ≤ LENGTH pf ∧
        (satisfiable (interp (run_proof fml (TAKE i pf))) ⇒
         satisfiable (interp (run_proof fml (TAKE j pf))))
  else F)
Proof
  strip_tac>>
  fs[installed_arm8_asl_def,check_unsat_code_def,cake_lpr_run_def]>>
  drule_all check_unsat_compiled_thm>>
  disch_then (qspec_then `ext` strip_assume_tac)>>
  goal_assum drule>>
  qpat_x_assum `result = _` SUBST_ALL_TAC>>
  gvs[]>>
  qexists_tac`out`>>
  qexists_tac`err`>>
  fs[check_unsat_sem_def]>>
  pop_assum mp_tac>>
  fs[CasePred "list"]>> strip_tac>> gvs[]>>
  drule TL_eq_hd_exists>> simp[]>>strip_tac>>gvs[]
  >- (
    (* 1 arg *)
    fs[check_unsat_1_sem_def]>>
    every_case_tac>>gvs[get_fml_def]>>rw[]>>
    simp[parse_dimacs_def])
  >- (
    (* 2 arg *)
    fs[check_unsat_2_sem_def]>>
    every_case_tac>>gvs[get_fml_def]>>rw[]>>
    simp[parse_dimacs_def]>>gvs[]>>
    match_mp_tac (GEN_ALL lpr_arrayParsingProgTheory.check_lpr_unsat_list_sound)>>
    first_x_assum (irule_at Any)>>
    gvs[]>>
    match_mp_tac (GEN_ALL parse_dimacs_wf)>>
    simp[parse_dimacs_def,AllCaseEqs()]>>
    metis_tac[])
  >- (
    (* 3 arg *)
    fs[check_unsat_3_sem_def]>>
    every_case_tac>>gvs[get_fml_def]>>rw[]>>
    simp[parse_dimacs_def]>>gvs[]>>
    match_mp_tac (GEN_ALL lpr_arrayParsingProgTheory.check_lpr_sat_equiv_list_sound)>>
    asm_exists_tac>>simp[]>>
    match_mp_tac (GEN_ALL parse_dimacs_wf)>>
    simp[parse_dimacs_def,AllCaseEqs()]>>
    metis_tac[])
  >- (
    (* 4 arg *)
    fs[check_unsat_4_sem_def]>>
    fs[CasePred "option"]>>
    rename1`get_fml fs f1 = SOME ff`>>
    PairCases_on`ff`>>gvs[CasePred "sum"]
    >- (
      (* -check *)
      pop_assum mp_tac >> IF_CASES_TAC>>simp[]>>
      fs[parse_rng_or_check_def,AllCaseEqs()]>>
      strip_tac>>simp[]>>
      gvs[get_fml_def,get_proof_def,AllCaseEqs()]>>
      drule parse_proof_toks_LENGTH>> rw[]>>gvs[]>>
      drule check_lines_success_str>>
      rw[]>>
      metis_tac[])>>
    gvs[parse_rng_or_check_def,AllCaseEqs()]>>
    rename1`parse_rng _ = SOME ij`>>
    Cases_on`ij`>>
    gvs[get_fml_def,get_proof_def,AllCaseEqs()]>>
    rw[]>>gvs[]>>
    simp[parse_dimacs_def,parse_proof_def]>>
    gvs[]>>
    match_mp_tac (GEN_ALL lpr_arrayParsingProgTheory.check_lpr_range_list_sound)>>
    first_x_assum (irule_at Any)>>
    `ff1 + 1 = LENGTH ff2 +1 ` by (
      fs[parse_dimacs_toks_def]>>
      qpat_x_assum `_ = SOME (x0,x1,x2)` mp_tac>>
      rpt (pop_assum kall_tac)>>
      every_case_tac>>fs[]>>
      drule LENGTH_parse_dimacs_body>>
      rw[]>> simp[])>>
    pop_assum SUBST_ALL_TAC>>
    first_x_assum (irule_at Any)>>
    fs[GSYM parse_proof_def]>>
    drule parse_proof_wf_proof>>
    simp[]>>
    `parse_dimacs (all_lines_file fs f1) = SOME ff2` by
      fs[parse_dimacs_def]>>
    drule parse_dimacs_wf>>simp[])
QED

Theorem run_proof_empty:
  run_proof fml [] = fml
Proof
  EVAL_TAC
QED

Theorem success_str_nonempty:
  success_str a b c ≠ «»
Proof
  EVAL_TAC
QED

Theorem Terminate_Success_IN_extend:
  Terminate Success io ∈ extend_with_resource_limit {Terminate Success io'} ⇔
  io = io'
Proof
  rw[extend_with_resource_limit_def]
QED

Theorem par_check_sound:
  EVERY (λ(cl,fs,mc,ms,i,j).
    cake_lpr_run cl fs mc ms ∧
    LENGTH cl = 5 ∧
    inFS_fname fs (EL 1 cl) ∧ inFS_fname fs (EL 2 cl) ∧
    file_content fs (EL 1 cl) = SOME fmlstr ∧
    file_content fs (EL 2 cl) = SOME pfstr ∧
    parse_rng_or_check (EL 3 cl) = SOME (INR (i,j))
  ) nodes ∧
  parse_dimacs (lines_of (strlit fmlstr)) = SOME fml ∧
  parse_proof (lines_of (strlit pfstr)) = SOME pf ∧
  interval_cover 0 (LENGTH pf) (MAP (λ(cl,fs,mc,ms,i,j). (i,j)) nodes)
  ⇒
  EVERY (λ(cl,fs,mc,ms,i,j).
    ∃io.
      machine_sem mc (basis_ffi ext cl fs) ms ⊆
      extend_with_resource_limit
        {Terminate Success io}) nodes ∧
  (
    EVERY (λ(cl,fs,mc,ms,i,j).
      ∃io.
      machine_sem mc (basis_ffi ext cl fs) ms = {Terminate Success io} ∧
      extract_fs ext (cl,fs) io =
        SOME (add_stdout fs
          (success_str (implode (md5 fmlstr)) (implode (md5 pfstr)) (print_rng i j)))
    ) nodes ⇒
    (satisfiable (interp fml) ⇒
     satisfiable (interp (run_proof fml pf)))
  )
Proof
  strip_tac>>
  sg `EVERY (λ(cl,fs,mc,ms,i,j).
  ∃io.
  machine_sem mc (basis_ffi ext cl fs) ms ⊆
    extend_with_resource_limit
      {Terminate Success io} ∧
  ∃out err.
    extract_fs ext (cl,fs) io =
      SOME (add_stdout (add_stderr fs err) out) ∧
    (out ≠ «» ⇒
      ∃fml pf.
      parse_dimacs (all_lines_file fs (EL 1 cl)) = SOME fml ∧
      parse_proof (all_lines_file fs (EL 2 cl)) = SOME pf ∧
      i ≤ j ∧ j ≤ LENGTH pf ∧
      (satisfiable (interp (run_proof fml (TAKE i pf))) ⇒
       satisfiable (interp (run_proof fml (TAKE j pf)))))) nodes`
  >- (
    fs[EVERY_MEM,FORALL_PROD]>>
    rw[]>>first_x_assum drule>>
    strip_tac>>
    drule machine_code_sound>> rpt(disch_then drule)>>
    simp[]>>  rpt(disch_then drule)>>
    disch_then (qspec_then `ext` strip_assume_tac)>>
    goal_assum drule>>
    goal_assum drule>>
    strip_tac>>gvs[])>>
  CONJ_TAC >- (
    pop_assum mp_tac>>match_mp_tac MONO_EVERY>>
    simp[FORALL_PROD]>>
    metis_tac[])>>
  rw[]>>
  drule interval_cover_satisfiable>>
  disch_then(qspecl_then[`pf`,`fml`] mp_tac)>>
  impl_tac>-(
    fs[EVERY_MEM,FORALL_PROD,MEM_MAP,EXISTS_PROD,PULL_EXISTS,run_proof_empty]>>
    rw[]>>rpt (first_x_assum drule)>>
    rw[]>>gvs[Terminate_Success_IN_extend]>>
    gs[SOME_11]>>
    fs[cake_lpr_run_def]>>
    drule STD_streams_stdout>>rw[]>>
    drule add_stdout_inj>>
    disch_then drule>>
    rw[]>>gvs[stdout_add_stderr]>>
    gvs[success_str_nonempty]>>
    imp_res_tac all_lines_file_lines_of>>
    gvs[])>>
  simp[]
QED

Definition check_successful_def:
  check_successful ext fmlstr pfstr (i:num,j:num) =
  ∃cl fs mc ms err io.
    cake_lpr_run cl fs mc ms ∧
    LENGTH cl = 5 ∧
    inFS_fname fs (EL 1 cl) ∧ inFS_fname fs (EL 2 cl) ∧
    file_content fs (EL 1 cl) = SOME fmlstr ∧
    file_content fs (EL 2 cl) = SOME pfstr ∧
    parse_rng_or_check (EL 3 cl) = SOME (INR (i,j)) ∧
    machine_sem mc (basis_ffi ext cl fs) ms = {Terminate Success io} ∧
    extract_fs ext (cl,fs) io =
      SOME (add_stdout (add_stderr fs err)
        (success_str (implode (md5 fmlstr)) (implode (md5 pfstr)) (print_rng i j)))
End

Theorem par_check_sound_2:
  parse_dimacs (lines_of (strlit fmlstr)) = SOME fml ∧
  parse_proof (lines_of (strlit pfstr)) = SOME pf ∧
  interval_cover 0 (LENGTH pf) ranges ∧
  EVERY (check_successful ext fmlstr pfstr) ranges ⇒
  (satisfiable (interp fml) ⇒ satisfiable (interp (run_proof fml pf)))
Proof
  rw[]>>
  drule interval_cover_satisfiable>>
  disch_then(qspecl_then[`pf`,`fml`] mp_tac)>>
  impl_tac>-(
    fs[EVERY_MEM,FORALL_PROD,MEM_MAP,EXISTS_PROD,PULL_EXISTS,run_proof_empty]>>
    rw[]>>first_x_assum drule>>
    simp[check_successful_def]>>rw[]>>
    drule machine_code_sound>> rpt(disch_then drule)>>
    simp[]>>  rpt(disch_then drule)>>
    rw[]>>
    imp_res_tac all_lines_file_lines_of>>
    fs[cake_lpr_run_def]>>
    drule STD_streams_stdout>>rw[]>>
    first_x_assum (qspec_then `ext` mp_tac)>>rw[]>>
    gvs[Terminate_Success_IN_extend]>>
    drule add_stdout_inj>>
    disch_then(qspec_then`out` mp_tac)>>
    rw[]>>gvs[stdout_add_stderr,success_str_nonempty])>>
  simp[]
QED

Theorem parse_proof_LENGTH:
  parse_proof ls = SOME pf ⇒
  LENGTH pf = LENGTH ls
Proof
  simp[parse_proof_def]>>
  rw[]>>
  drule parse_proof_toks_LENGTH>>
  simp[]
QED

Theorem success_str_inj:
  success_str a b c = success_str a b d ⇒ c = d
Proof
  rw[success_str_def,expected_prefix_def]>>
  pop_assum mp_tac>>
  EVAL_TAC>>
  rw[]>>simp[]>>
  every_case_tac>>fs[]
QED

Definition check_successful_par_def:
  check_successful_par ext fmlstr pfstr =
  ∃outstr.
    (∀out. MEM out outstr ⇒
    (∃cl fs mc ms err io.
      cake_lpr_run cl fs mc ms ∧
      LENGTH cl = 5 ∧
      inFS_fname fs (EL 1 cl) ∧ inFS_fname fs (EL 2 cl) ∧
      file_content fs (EL 1 cl) = SOME fmlstr ∧
      file_content fs (EL 2 cl) = SOME pfstr ∧
      machine_sem mc (basis_ffi ext cl fs) ms = {Terminate Success io} ∧
      extract_fs ext (cl,fs) io =
        SOME (add_stdout (add_stderr fs err) out))) ∧
    (∃cl fs mc ms io.
      cake_lpr_run cl fs mc ms ∧
      LENGTH cl = 5 ∧
      inFS_fname fs (EL 1 cl) ∧ inFS_fname fs (EL 2 cl) ∧
      file_content fs (EL 1 cl) = SOME fmlstr ∧
      file_content fs (EL 2 cl) = SOME pfstr ∧
      all_lines_file fs (EL 4 cl) = outstr ∧
      machine_sem mc (basis_ffi ext cl fs) ms = {Terminate Success io} ∧
      extract_fs ext (cl,fs) io =
        SOME (add_stdout fs
          (concat [«s VERIFIED INTERVALS COVER 0-» ; toString (LENGTH (lines_of (strlit pfstr))); «\n»])))
End

Theorem par_check_sound_3:
  parse_dimacs (lines_of (strlit fmlstr)) = SOME fml ∧
  parse_proof (lines_of (strlit pfstr)) = SOME pf ∧
  check_successful_par ext fmlstr pfstr ⇒
  (satisfiable (interp fml) ⇒ satisfiable (interp (run_proof fml pf)))
Proof
  rw[check_successful_par_def]>>
  (* The run with -check *)
  drule machine_code_sound>> rpt(disch_then drule)>>
  simp[]>>  rpt(disch_then drule)>>
  rw[]>>
  `STD_streams fs` by fs[cake_lpr_run_def]>>
  drule STD_streams_stdout>>rw[]>>
  first_x_assum (qspec_then `ext` mp_tac)>>rw[]>>
  gvs[Terminate_Success_IN_extend]>>
  drule add_stdout_inj>>
  disch_then drule>>
  simp[stdout_add_stderr]>>
  rw[]>>fs[concat_success_str]>>
  qpat_x_assum`_ ⇒ _` mp_tac>>
  impl_tac >- simp[mlstringTheory.concat_def]>>
  every_case_tac>>rw[]>>
  drule lpr_composeProgTheory.check_lines_correct>>
  rw[]>>
  qpat_x_assum`satisfiable _` mp_tac>>
  match_mp_tac (GEN_ALL par_check_sound_2)>>
  asm_exists_tac>> simp[]>>
  asm_exists_tac>> simp[]>>
  drule parse_proof_LENGTH>>
  imp_res_tac all_lines_file_lines_of>>
  rw[]>>
  gs[]>>
  asm_exists_tac>> simp[]>>
  qexists_tac`ext`>>
  simp[EVERY_MEM,FORALL_PROD]>>
  rw[]>>
  fs[SUBSET_DEF]>>first_x_assum drule>>
  strip_tac>>
  drule MEM_get_ranges>>
  disch_then drule>>
  simp[GSYM success_str_def]>>
  strip_tac>>
  (* The run with a given range *)
  first_x_assum drule>>
  strip_tac >>
  simp[check_successful_def]>>
  rpt(asm_exists_tac>>simp[])>>
  drule machine_code_sound>>
  rpt(disch_then drule)>>simp[]>>
  strip_tac>>first_x_assum (qspec_then `ext` mp_tac)>>rw[]>>fs[]>>
  gvs[Terminate_Success_IN_extend]>>
  qmatch_asmsub_abbrev_tac`add_stdout (add_stderr fs' _) ss`>>
  `ss = out''` by (
    fs[cake_lpr_run_def]>>
    drule STD_streams_stdout>>rw[]>>
    drule add_stdout_inj>>
    disch_then match_mp_tac>>
    metis_tac[stdout_add_stderr])>>
  unabbrev_all_tac>>
  gvs[success_str_nonempty]>>
  pop_assum mp_tac>>every_case_tac>>gvs[]
  >-
    metis_tac[concat_success_str]>>
  rw[]>>
  qmatch_asmsub_rename_tac`print_rng i j`>>
  `out' = print_rng i j` by
    metis_tac[success_str_inj]>>
  rveq>>
  fs[parse_rng_print_rng]>>
  metis_tac[stdout_add_stderr]
QED
