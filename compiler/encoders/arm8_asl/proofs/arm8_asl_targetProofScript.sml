(*
  Prove `encoder_correct` for ASL-derived ARMv8
*)
Theory arm8_asl_targetProof
Ancestors
  arm8 armv86a_termination[qualified] l3_equivalenceProof
  arm8_target arm8_asl_target list words finite_map asmProps
  arm8_step arm8_targetProof l3_equivalence l3_equivalence_lemmas
Libs
  BasicProvers dep_rewrite wordsLib asmLib arm8_targetProofLib
  l3_equivalenceLib

val _ = wordsLib.guess_lengths();
val _ = wordsLib.output_words_as_hex();

(*
val _ = set_trace "Goalstack.howmany_printed_subgoals" 1;
*)

(********** Lemmas **********)

Theorem arm8_asl_ok_def:
  arm8_asl_ok asl ⇔
    asl_sys_regs_ok asl ∧
    (PSTATE_ref.read_from asl.regstate).ProcState_EL = 0w ∧ (* EL0 *)
    ¬word_bit 4 (SCTLR_EL1_ref.read_from asl.regstate) ∧ (* ¬SCTLR_EL1.SA0 *)
    ¬word_bit 24 (SCTLR_EL1_ref.read_from asl.regstate) ∧ (* ¬SCTLR_EL1.EOE *)
    ¬word_bit 37 (TCR_EL1_ref.read_from asl.regstate) ∧ (* ¬TCR_EL1.TBI0 *)
    ¬word_bit 38 (TCR_EL1_ref.read_from asl.regstate) ∧ (* ¬TCR_EL1.TBI1 *)
    aligned 2 (PC_ref.read_from asl.regstate) ∧ (* aligned 2 PC *)
    arm8_asl_mem_ok asl ∧ arm8_asl_regs_ok asl
Proof
  rw[arm8_asl_ok_def] >>
  eq_tac >> simp[] >> EVAL_TAC >> rw[]
QED

Theorem arm8_asl_proj_def:
  arm8_asl_proj (memory : word64 set) asl = (
    PSTATE_ref.read_from asl.regstate,
    SCTLR_EL1_ref.read_from asl.regstate,
    TCR_EL1_ref.read_from asl.regstate,
    R_ref.read_from asl.regstate,
    fun2set ($' asl.memstate o w2n, memory),
    PC_ref.read_from asl.regstate,
    asl_sys_regs_ok asl,
    arm8_asl_mem_ok asl,
    arm8_asl_regs_ok asl
    )
Proof
  EVAL_TAC >> eq_tac >> rw[]
QED

Theorem exists_state_rel:
  ∀asl. arm8_asl_regs_ok asl ∧ arm8_asl_mem_ok asl ⇔ ∃l3. state_rel l3 asl
Proof
  gen_tac >> simp[arm8_asl_regs_ok_def, arm8_asl_mem_ok_def] >> reverse eq_tac
  >- (
    strip_tac >> state_rel_tac[] >>
    first_x_assum $ qspec_then `w` assume_tac >> gvs[] >>
    goal_assum drule >> simp[]
    ) >>
  rw[arm8Theory.EXISTS_arm8_state] >> state_rel_tac[] >>
  qexistsl_tac [
    `λw. v2w $ (MAP (THE o bool_of_bitU)) (THE (FLOOKUP asl.memstate (w2n w)))`,
    `let pstate = asl.regstate.ProcState_reg "PSTATE" in
     <| EL := pstate.ProcState_EL
      ; SPS := word_bit 0 pstate.ProcState_SP
      ; N := word_bit 0 pstate.ProcState_N
      ; Z := word_bit 0 pstate.ProcState_Z
      ; C := word_bit 0 pstate.ProcState_C
      ; V := word_bit 0 pstate.ProcState_V
      |>`,
    `λw. EL (w2n w) (asl.regstate.vector_31_inc_bitvector_64_dec_reg "_R")`,
    `rec'SCTLRType ((31 >< 0) (asl.regstate.bitvector_64_dec_reg "SCTLR_EL1"))`,
    `rec'SCTLRType ((31 >< 0) (asl.regstate.bitvector_64_dec_reg "SCTLR_EL2"))`,
    `rec'SCTLRType ((31 >< 0) (asl.regstate.bitvector_64_dec_reg "SCTLR_EL3"))`,
    `rec'TCR_EL1 (asl.regstate.bitvector_64_dec_reg "TCR_EL1")`,
    `rec'TCR_EL2_EL3 ((31 >< 0) (asl.regstate.bitvector_64_dec_reg "TCR_EL2"))`,
    `rec'TCR_EL2_EL3 (asl.regstate.bitvector_32_dec_reg "TCR_EL3")`,
    `if asl.regstate.bool_reg "__BranchTaken" then SOME ARB else NONE`
    ] >>
  simp[] >> rw[]
  >- blastLib.BBLAST_TAC
  >- blastLib.BBLAST_TAC
  >- blastLib.BBLAST_TAC
  >- blastLib.BBLAST_TAC
  >- blastLib.BBLAST_TAC
  >- (
    simp[arm8Theory.rec'SCTLRType_def] >>
    blastLib.BBLAST_TAC
    )
  >- (
    simp[arm8Theory.rec'SCTLRType_def] >>
    blastLib.BBLAST_TAC
    )
  >- (
    simp[arm8Theory.rec'SCTLRType_def] >>
    blastLib.BBLAST_TAC
    )
  >- (
    simp[arm8Theory.rec'TCR_EL1_def] >>
    blastLib.BBLAST_TAC
    )
  >- (
    simp[arm8Theory.rec'TCR_EL2_EL3_def] >>
    blastLib.BBLAST_TAC
    )
  >- (
    simp[arm8Theory.rec'TCR_EL2_EL3_def] >>
    blastLib.BBLAST_TAC
    )
  >- (
    ntac 2 $ first_x_assum $ qspec_then `w` assume_tac >> gvs[] >>
    irule_at Any EQ_REFL >> simp[listTheory.MAP_MAP_o, combinTheory.o_DEF]
    )
QED

Theorem exists_state_rel_sym:
  ∀l3. l3.exception = NoException ⇒ ∃asl. state_rel l3 asl
Proof
  rw[] >>
  simp[sail2_state_monadTheory.EXISTS_sequential_state,
       armv86a_typesTheory.EXISTS_regstate] >>
  state_rel_tac[] >>
  map_every qmatch_goalsub_abbrev_tac [
    `a = (_ >< _) (_ "SCTLR_EL1")`,`b = (_ >< _) (_ "SCTLR_EL2")`,
    `c = (_ >< _) (_ "SCTLR_EL3")`,`d = _ "TCR_EL1"`,
    `e = (_ >< _) (_ "TCR_EL2")`,`f = (_ >< _) (_ "TCR_EL3")`] >>
  rpt $ pop_assum kall_tac >>
  qexistsl_tac [
    `λs. if s ≠ "PSTATE" then ARB else <|
        ProcState_EL := l3.PSTATE.EL
      ; ProcState_SP := v2w [l3.PSTATE.SPS]
      ; ProcState_N := v2w [l3.PSTATE.N]
      ; ProcState_Z := v2w [l3.PSTATE.Z]
      ; ProcState_C := v2w [l3.PSTATE.C]
      ; ProcState_V := v2w [l3.PSTATE.V] |>`,
    `λs. if s ≠ "TCR_EL3" then ARB else f`,
    `λs.  if s = "SP_EL0" then l3.SP_EL0
     else if s = "SP_EL1" then l3.SP_EL1
     else if s = "SP_EL2" then l3.SP_EL2
     else if s = "SP_EL3" then l3.SP_EL3
     else if s = "SCTLR_EL1" then w2w a
     else if s = "SCTLR_EL2" then w2w b
     else if s = "SCTLR_EL3" then w2w c
     else if s = "_PC" then l3.PC
     else if s = "TCR_EL1" then d
     else if s = "TCR_EL2" then w2w e
     else if s = "TCR_EL3" then w2w f else ARB`,
     `λs. if s ≠ "__BranchTaken" then ARB else IS_SOME l3.branch_hint`,
     `λs. if s ≠ "_R" then ARB else GENLIST (l3.REG o n2w) 32`,
     `FUN_FMAP (λn. MAP bitU_of_bool (w2v (l3.MEM (n2w n)))) (count (dimword(:64)))`,
     `FUN_FMAP (K B0) (count (dimword(:64)))`
     ] >>
  simp[GSYM PULL_EXISTS] >> ntac 5 (conj_tac >- WORD_DECIDE_TAC) >>
  conj_tac
  >- (
    rw[] >> gvs[arithmeticTheory.LE_LT1] >>
    rpt (pop_assum mp_tac >> simp[Once NUMERAL_LESS_THM] >> strip_tac >> gvs[])
    ) >>
  gen_tac >> DEP_REWRITE_TAC[FLOOKUP_FUN_FMAP] >> simp[] >>
  qspec_then `w` assume_tac w2n_lt >> gvs[] >>
  irule_at Any EQ_REFL >> simp[]
QED

Theorem arm8_asl_ok:
  ∀asl. arm8_asl_ok asl ⇔
    asl_sys_regs_ok asl ∧
    ∃l3. state_rel l3 asl ∧ arm8_ok l3
Proof
  rw[arm8_asl_ok_def] >> eq_tac >> strip_tac >> simp[]
  >- (
    drule_all $ iffLR exists_state_rel >> rw[] >>
    goal_assum drule >> rw[arm8_ok_def]
    >- state_rel_tac[]
    >- (
      gvs[state_rel_def, read_rel_def, sctlr_rel_def] >>
      qpat_x_assum `¬word_bit 24 (SCTLR_EL1_ref.read_from _)` mp_tac >>
      qpat_x_assum `reg'SCTLRType l3.SCTLR_EL1 = _` mp_tac >>
      simp[arm8Theory.reg'SCTLRType_def] >> CASE_TAC >> simp[] >>
      blastLib.BBLAST_TAC
      )
    >- (
      gvs[state_rel_def, read_rel_def, sctlr_rel_def] >>
      qpat_x_assum `¬word_bit 4 (SCTLR_EL1_ref.read_from _)` mp_tac >>
      qpat_x_assum `reg'SCTLRType l3.SCTLR_EL1 = _` mp_tac >>
      simp[arm8Theory.reg'SCTLRType_def] >> CASE_TAC >> simp[] >>
      blastLib.BBLAST_TAC
      )
    >- (
      gvs[state_rel_def, read_rel_def, tcr_el1_rel_def] >>
      qpat_x_assum `¬word_bit 38 (TCR_EL1_ref.read_from _)` mp_tac >>
      qpat_x_assum `reg'TCR_EL1 l3.TCR_EL1 = _` mp_tac >>
      simp[arm8Theory.reg'TCR_EL1_def] >> CASE_TAC >> simp[] >>
      blastLib.BBLAST_TAC
      )
    >- (
      gvs[state_rel_def, read_rel_def, tcr_el1_rel_def] >>
      qpat_x_assum `¬word_bit 37 (TCR_EL1_ref.read_from _)` mp_tac >>
      qpat_x_assum `reg'TCR_EL1 l3.TCR_EL1 = _` mp_tac >>
      simp[arm8Theory.reg'TCR_EL1_def] >> CASE_TAC >> simp[] >>
      blastLib.BBLAST_TAC
      )
    >- state_rel_tac[]
    >- state_rel_tac[]
    )
  >- (
    drule $ SIMP_RULE std_ss [PULL_EXISTS] $ iffRL exists_state_rel >> simp[] >>
    gvs[arm8_ok_def] >> rw[]
    >- state_rel_tac[]
    >- (
      gvs[state_rel_def, read_rel_def, sctlr_rel_def] >>
      qpat_x_assum `¬l3.SCTLR_EL1.SA0` mp_tac >>
      qpat_x_assum `reg'SCTLRType l3.SCTLR_EL1 = _` mp_tac >>
      simp[arm8Theory.reg'SCTLRType_def] >> CASE_TAC >> simp[] >>
      blastLib.BBLAST_TAC
      )
    >- (
      gvs[state_rel_def, read_rel_def, sctlr_rel_def] >>
      qpat_x_assum `¬l3.SCTLR_EL1.E0E` mp_tac >>
      qpat_x_assum `reg'SCTLRType l3.SCTLR_EL1 = _` mp_tac >>
      simp[arm8Theory.reg'SCTLRType_def] >> CASE_TAC >> simp[] >>
      blastLib.BBLAST_TAC
      )
    >- (
      gvs[state_rel_def, read_rel_def, tcr_el1_rel_def] >>
      qpat_x_assum `¬l3.TCR_EL1.TBI0` mp_tac >>
      qpat_x_assum `reg'TCR_EL1 l3.TCR_EL1 = _` mp_tac >>
      simp[arm8Theory.reg'TCR_EL1_def] >> CASE_TAC >> simp[] >>
      blastLib.BBLAST_TAC
      )
    >- (
      gvs[state_rel_def, read_rel_def, tcr_el1_rel_def] >>
      qpat_x_assum `¬l3.TCR_EL1.TBI1` mp_tac >>
      qpat_x_assum `reg'TCR_EL1 l3.TCR_EL1 = _` mp_tac >>
      simp[arm8Theory.reg'TCR_EL1_def] >> CASE_TAC >> simp[] >>
      blastLib.BBLAST_TAC
      )
    >- state_rel_tac[]
    )
QED

Theorem state_rel_unique:
  state_rel l3 asl ∧ state_rel l3' asl ⇒
  ∃hint.  l3' = l3 with branch_hint := OPTION_MAP hint l3.branch_hint
Proof
  rw[arm8_state_component_equality] >>
  qexists_tac `K (THE l3'.branch_hint)` >> rw[]
  >- (
    rw[FUN_EQ_THM] >> state_rel_tac[] >>
    ntac 2 $ first_x_assum $ qspec_then `x` assume_tac >> gvs[] >>
    AP_TERM_TAC >> gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN] >> rw[LIST_EQ_REWRITE] >>
    first_x_assum drule >> simp[sail2_valuesTheory.bitU_of_bool_def] >> rw[]
    )
  >- state_rel_tac[]
  >- (
    simp[ProcState_component_equality] >> state_rel_tac[] >>
    rpt $ qpat_x_assum `v2w [_] = v2w [_] : word1` mp_tac >> blastLib.BBLAST_TAC
    )
  >- (
    rw[FUN_EQ_THM] >> state_rel_tac[] >>
    ntac 2 $ first_x_assum $ qspec_then `w2n x` mp_tac >> simp[] >>
    impl_tac >> rw[] >> qspec_then `x` mp_tac w2n_lt >> simp[]
    )
  >- (
    gvs[state_rel_def, read_rel_def, sctlr_rel_def] >>
    ntac 2 $ qpat_x_assum `reg'SCTLRType _.SCTLR_EL1 = _` mp_tac >>
    simp[reg'SCTLRType_def] >> ntac 2 CASE_TAC >> simp[] >>
    blastLib.BBLAST_TAC
    )
  >- (
    gvs[state_rel_def, read_rel_def, sctlr_rel_def] >>
    ntac 2 $ qpat_x_assum `reg'SCTLRType _.SCTLR_EL2 = _` mp_tac >>
    simp[reg'SCTLRType_def] >> ntac 2 CASE_TAC >> simp[] >>
    blastLib.BBLAST_TAC
    )
  >- (
    gvs[state_rel_def, read_rel_def, sctlr_rel_def] >>
    ntac 2 $ qpat_x_assum `reg'SCTLRType _.SCTLR_EL3 = _` mp_tac >>
    simp[reg'SCTLRType_def] >> ntac 2 CASE_TAC >> simp[] >>
    blastLib.BBLAST_TAC
    )
  >- gvs[state_rel_def, read_rel_def]
  >- gvs[state_rel_def, read_rel_def]
  >- gvs[state_rel_def, read_rel_def]
  >- gvs[state_rel_def, read_rel_def]
  >- (
    gvs[state_rel_def, read_rel_def, tcr_el1_rel_def] >>
    ntac 2 $ qpat_x_assum `reg'TCR_EL1 _.TCR_EL1 = _` mp_tac >>
    simp[reg'TCR_EL1_def] >> ntac 2 CASE_TAC >> simp[] >>
    blastLib.BBLAST_TAC
    )
  >- (
    gvs[state_rel_def, read_rel_def, tcr_el2_3_rel_def] >>
    ntac 2 $ qpat_x_assum `reg'TCR_EL2_EL3 _.TCR_EL2 = _` mp_tac >>
    simp[reg'TCR_EL2_EL3_def] >> ntac 2 CASE_TAC >> simp[] >>
    blastLib.BBLAST_TAC
    )
  >- (
    gvs[state_rel_def, read_rel_def, tcr_el2_3_rel_def] >>
    ntac 2 $ qpat_x_assum `reg'TCR_EL2_EL3 _.TCR_EL3 = _` mp_tac >>
    simp[reg'TCR_EL2_EL3_def] >> ntac 2 CASE_TAC >> simp[] >>
    blastLib.BBLAST_TAC
    )
  >- (
    gvs[state_rel_def, read_rel_def, branch_hint_rel_def] >>
    Cases_on `l3.branch_hint` >> gvs[] >>
    Cases_on `l3'.branch_hint` >> gvs[]
    )
  >- gvs[state_rel_def]
QED

Theorem l3_asl_target_state_rel:
  ∀l3 asl.  state_rel l3 asl ∧ asl_sys_regs_ok asl ⇒
    (target_state_rel arm8_target s1 l3 ⇔ target_state_rel arm8_asl_target s1 asl)
Proof
  rw[] >> simp[target_state_rel_def] >>
  simp[arm8_target_def, arm8_asl_target_def] >>
  simp[arm8_asl_ok, PULL_EXISTS, GSYM CONJ_ASSOC] >> eq_tac >> strip_tac >> simp[]
  >- (
    goal_assum drule >> simp[] >> state_rel_tac[]
    >- (
      first_x_assum $ drule o GSYM >> rw[] >>
      first_x_assum $ qspec_then `a` assume_tac >> gvs[] >>
      gvs[FLOOKUP_DEF] >> simp[MAP_MAP_o, combinTheory.o_DEF]
      )
    >- (
      first_x_assum $ drule_all o GSYM >> rw[] >>
      last_x_assum $ qspec_then `i` mp_tac >>
      impl_tac >> simp[] >> gvs[arm8_config_def]
      )
    >- gvs[arm8_config_def]
    )
  >- (
    drule state_rel_unique >> disch_then $ qspec_then `l3` assume_tac >> gvs[] >>
    rw[]
    >- gvs[arm8_ok_def]
    >- state_rel_tac[]
    >- (
      state_rel_tac[] >>
      first_x_assum $ drule o GSYM >> rw[] >>
      first_x_assum $ qspec_then `a` assume_tac >> gvs[FLOOKUP_DEF] >>
      simp[MAP_MAP_o, combinTheory.o_DEF]
      )
    >- (
      first_x_assum $ drule_all o GSYM >> rw[] >> gvs[arm8_config_def] >>
      state_rel_tac[]
      )
    >- gvs[arm8_config_def]
    )
QED

Triviality exists_arm8_ok:
  ∀s asl.  target_state_rel arm8_asl_target s asl ⇒
    ∃l3. state_rel l3 asl ∧ arm8_ok l3 ∧
         target_state_rel arm8_target s l3
Proof
  rw[] >>
  `arm8_asl_ok asl` by gvs[target_state_rel_def, arm8_asl_target_def] >>
  gvs[arm8_asl_ok] >> goal_assum drule >> simp[] >>
  irule $ iffRL l3_asl_target_state_rel >> rpt $ goal_assum drule
QED

Triviality l3_asl_arm8_encode_fail[simp]:
  ∀instr. MEM instr arm8_target$arm8_encode_fail ⇒ l3_models_asl_instr instr
Proof
  rw[arm8_encode_fail_def] >> simp[l3_models_asl_NoOperation]
QED

Theorem l3_asl_arm8_load_store_ast:
  ∀instr ls r1 r2 a.
    MEM instr (arm8_target$arm8_load_store_ast ls r1 r2 a) ∧
    ls ≠ MemOp_PREFETCH ∧
    (∀s. Encode instr ≠ BadCode s)
  ⇒ l3_models_asl_instr instr
Proof
  rw[arm8_load_store_ast_def] >> gvs[]
  >- (
    irule l3_models_asl_AddSubImmediate >> simp[] >>
    gvs[encode_rws] >> every_case_tac >> gvs[]
    )
  >~ [`AddSubImmediate@64`]
  >- (
    irule l3_models_asl_AddSubImmediate >> simp[] >>
    gvs[encode_rws] >> every_case_tac >> gvs[]
    ) >>
  (
    Cases_on `ls` >> gvs[]
    >- ( (* Load *)
      irule $ SIMP_RULE std_ss [LET_DEF]
        l3_models_asl_LoadStoreImmediate_NORMAL_LOAD_FFFFF >>
      simp[]
      )
    >- ( (* Store *)
      irule $ SIMP_RULE std_ss [LET_DEF]
        l3_models_asl_LoadStoreImmediate_NORMAL_STORE_FFFFF >>
      simp[]
      )
  )
QED

Theorem l3_asl_arm8_load_store_ast32:
  ∀instr ls r1 r2 a.
    MEM instr (arm8_target$arm8_load_store_ast32 ls r1 r2 a) ∧
    ls ≠ MemOp_PREFETCH ∧
    (∀s. Encode instr ≠ BadCode s)
  ⇒ l3_models_asl_instr instr
Proof
  rw[arm8_load_store_ast32_def] >> gvs[]
  >- (
    irule l3_models_asl_AddSubImmediate >> simp[] >>
    gvs[encode_rws] >> every_case_tac >> gvs[]
    )
  >~ [`AddSubImmediate@64`]
  >- (
    irule l3_models_asl_AddSubImmediate >> simp[] >>
    gvs[encode_rws] >> every_case_tac >> gvs[]
    ) >>
  (
    Cases_on `ls` >> gvs[]
    >- ( (* Load32 *)
      irule $ SIMP_RULE std_ss [LET_DEF]
        l3_models_asl_LoadStoreImmediate_32_NORMAL_LOAD_FFFFF >>
      simp[]
      )
    >- ( (* Store32 *)
      irule $ SIMP_RULE std_ss [LET_DEF]
        l3_models_asl_LoadStoreImmediate_32_NORMAL_STORE_FFFFF >>
      simp[]
      )
  )
QED

Theorem l3_asl_arm8_ast:
  ∀instr prog.
    MEM instr (arm8_target$arm8_ast prog) ∧
    (∀s. Encode instr ≠ BadCode s)
  ⇒ l3_models_asl_instr instr
Proof
  rpt gen_tac >> Cases_on `prog` >> simp[arm8_ast_def]
  >- ( (* Inst *)
    Cases_on `i` >> simp[arm8_ast_def] >> rw[]
    >- simp[l3_models_asl_NoOperation] (* Skip *)
    >- ( (* Const - 1 *)
      gvs[arm8_enc_mov_imm_def] >>
      every_case_tac >> gvs[l3_models_asl_MoveWideOp_Z, l3_models_asl_MoveWideOp_N] >>
      irule l3_models_asl_LogicalImmediate >> simp[EncodeLogicalOp_def]
      )
    >- ( (* Const - 2 *)
      gvs[arm8_enc_mov_imm_def] >>
      every_case_tac >>
      gvs[l3_models_asl_MoveWideOp_Z,
          l3_models_asl_MoveWideOp_N, l3_models_asl_MoveWideOp_K]
      )
    >- ( (* Arith *)
      Cases_on `a` >> gvs[arm8_ast_def]
      >- ( (* Binop *)
        Cases_on `r` >> gvs[arm8_ast_def]
        >- ( (* Reg *)
          Cases_on `b` >> simp[]
          >- simp[l3_models_asl_AddSubShiftedRegister] (* Add *)
          >- simp[l3_models_asl_AddSubShiftedRegister] (* Sub *) >>
          (* And, Or, Xor *)
          irule l3_models_asl_LogicalShiftedRegister >>
          simp[EncodeLogicalOp_def, bop_enc_def]
          )
        >- ( (* Imm *)
          Cases_on `b` >> gvs[]
          >- ( (* Add *)
            irule l3_models_asl_AddSubImmediate >> gvs[encode_rws] >>
            every_case_tac >> gvs[]
            )
          >- ( (* Sub *)
            irule l3_models_asl_AddSubImmediate >> gvs[encode_rws] >>
            every_case_tac >> gvs[]
            )
          >- ( (* And *)
            irule l3_models_asl_LogicalImmediate >>
            simp[EncodeLogicalOp_def, bop_enc_def] >>
            gvs[encode_rws] >> every_case_tac >> gvs[]
            )
          >- ( (* Or *)
            irule l3_models_asl_LogicalImmediate >>
            simp[EncodeLogicalOp_def, bop_enc_def] >>
            gvs[encode_rws] >> every_case_tac >> gvs[]
            )
          >- ( (* Xor *)
            IF_CASES_TAC >> gvs[]
            >- (
              irule l3_models_asl_LogicalShiftedRegister >>
              simp[EncodeLogicalOp_def, bop_enc_def]
              )
            >- (
              irule l3_models_asl_LogicalImmediate >>
              simp[EncodeLogicalOp_def, bop_enc_def] >>
              gvs[encode_rws] >> every_case_tac >> gvs[]
              )
            )
          )
        )
      >- ( (* Shift *)
        Cases_on `s` >> gvs[arm8_ast_def]
        >- ( (* Lsl *)
          every_case_tac >> gvs[] >>
          irule l3_models_asl_BitfieldMove >> simp[] >> WORD_DECIDE_TAC
          )
        >- ( (* Lsr *)
          every_case_tac >> gvs[] >>
          irule l3_models_asl_BitfieldMove >> simp[] >>
          gvs[encode_rws] >> every_case_tac >> gvs[]
          )
        >- ( (* Asr *)
          every_case_tac >> gvs[] >>
          irule l3_models_asl_BitfieldMove >> simp[] >>
          gvs[encode_rws] >> every_case_tac >> gvs[]
          )
        >- simp[l3_models_asl_ExtractRegister] (* Ror *)
        )
      >- simp[l3_models_asl_Division] (* Div *)
      >- simp[l3_models_asl_MultiplyHigh] (* LongMul - 1 *)
      >- simp[l3_models_asl_MultiplyAddSub] (* LongMul - 2 *)
      >- simp[l3_models_asl_AddSubImmediate] (* AddCarry - 1 *)
      >- simp[l3_models_asl_ConditionalCompareImmediate] (* AddCarry - 2 *)
      >- simp[l3_models_asl_AddSubCarry] (* AddCarry - 3 *)
      >- simp[l3_models_asl_MoveWideOp_Z] (* AddCarry - 4 *)
      >- simp[l3_models_asl_AddSubCarry] (* AddCarry - 5 *)
      >- simp[l3_models_asl_AddSubShiftedRegister] (* AddOverflow - 1 *)
      >- simp[l3_models_asl_ConditionalSelect] (* AddOverflow - 2 *)
      >- simp[l3_models_asl_AddSubShiftedRegister] (* SubOverflow - 1 *)
      >- simp[l3_models_asl_ConditionalSelect] (* SubOverflow - 2 *)
      )
    >- ( (* Mem *)
      Cases_on `m` >>
      gvs[arm8_ast_def]
      >- ( (* Load *)
        Cases_on `a` >> gvs[arm8_ast_def] >>
        irule l3_asl_arm8_load_store_ast >> simp[] >>
        goal_assum $ drule_at Any >> simp[]
        )
      >- ( (* Load8 *)
        Cases_on `a` >> gvs[arm8_ast_def] >>
        irule $ SIMP_RULE std_ss [LET_DEF]
          l3_models_asl_LoadStoreImmediate_8_NORMAL_LOAD_FFFFF >>
        simp[]
        )
      >- ( (* Load32 *)
        Cases_on `a` >> gvs[arm8_ast_def] >>
        irule l3_asl_arm8_load_store_ast32 >> simp[] >>
        goal_assum $ drule_at Any >> simp[]
        )
      >- ( (* Store *)
        Cases_on `a` >> gvs[arm8_ast_def] >>
        irule l3_asl_arm8_load_store_ast >> simp[] >>
        goal_assum $ drule_at Any >> simp[]
        )
      >- ( (* Store8 *)
        Cases_on `a` >> gvs[arm8_ast_def] >>
        irule $ SIMP_RULE std_ss [LET_DEF]
          l3_models_asl_LoadStoreImmediate_8_NORMAL_STORE_FFFFF >>
        simp[]
        )
      >- ( (* Store32 *)
        Cases_on `a` >> gvs[arm8_ast_def] >>
        irule l3_asl_arm8_load_store_ast32 >> simp[] >>
        goal_assum $ drule_at Any >> simp[]
        )
      )
    )
  >- ( (* Jump *)
    rw[] >> irule l3_models_asl_BranchImmediate_JMP >>
    gvs[encode_rws] >> pop_assum mp_tac >> IF_CASES_TAC >> simp[]
    )
  >- ( (* JumpCmp *)
    Cases_on `r` >> gvs[arm8_ast_def] >> rw[]
    >- ( (* Reg - 1 *)
      irule l3_models_asl_LogicalShiftedRegister >>
      simp[EncodeLogicalOp_def]
      )
    >- ( (* Reg - 2 *)
      irule l3_models_asl_BranchConditional >>
      conj_tac >- gvs[asmSemTheory.is_test_def, cmp_cond_def] >>
      gvs[encode_rws] >> pop_assum mp_tac >> IF_CASES_TAC >> gvs[]
      )
    >- simp[l3_models_asl_AddSubShiftedRegister] (* Reg - 3 *)
    >- ( (* Reg - 4 *)
      irule l3_models_asl_BranchConditional >>
      conj_tac >- (Cases_on `c` >> gvs[asmSemTheory.is_test_def, cmp_cond_def]) >>
      gvs[encode_rws] >> pop_assum mp_tac >> IF_CASES_TAC >> gvs[]
      )
    >- ( (* Imm - 1 *)
      irule l3_models_asl_LogicalImmediate >>
      simp[EncodeLogicalOp_def] >> gvs[encode_rws] >> every_case_tac >> gvs[]
      )
    >- ( (* Imm - 2 *)
      irule l3_models_asl_BranchConditional >>
      conj_tac >- gvs[asmSemTheory.is_test_def, cmp_cond_def] >>
      gvs[encode_rws] >> pop_assum mp_tac >> IF_CASES_TAC >> gvs[]
      )
    >- ( (* Imm - 3 *)
      irule l3_models_asl_AddSubImmediate >>
      gvs[encode_rws] >> every_case_tac >> gvs[]
      )
    >- (
      irule l3_models_asl_BranchConditional >>
      conj_tac >- (Cases_on `c` >> gvs[asmSemTheory.is_test_def, cmp_cond_def]) >>
      gvs[encode_rws] >> pop_assum mp_tac >> IF_CASES_TAC >> gvs[]
      )
    )
  >- ( (* Call *)
    rw[] >> irule l3_models_asl_BranchImmediate_CALL >>
    gvs[encode_rws] >> pop_assum mp_tac >> IF_CASES_TAC >> gvs[]
    )
  >- simp[l3_models_asl_BranchRegister_JMP] (* JumpReg *)
  >- ( (* Loc *)
    rw[] >> simp[l3_models_asl_MoveWideOp_K]
    >- simp[l3_models_asl_Address |> SIMP_RULE std_ss [LET_DEF]]
    >- simp[l3_models_asl_Address |> SIMP_RULE std_ss [LET_DEF]]
    >- simp[l3_models_asl_AddSubShiftedRegister]
    )
QED

Theorem l3_asl_interference_ok:
  ∀env m l3 asl.
    interference_ok env (arm8_asl_proj m) ∧ state_rel l3 asl
    ⇒ ∃l3_env.
        interference_ok l3_env (arm8_proj m) ∧
        ∀i. state_rel (l3_env i l3) (env i asl)
Proof
  rw[] >>
  qexists_tac
    `λi l3.
      let asl' = (env i asl).regstate in
      l3 with <|
          MEM := (
            λw. if m w then l3.MEM w else
            v2w (MAP (THE o bool_of_bitU) $ (env i asl).memstate ' (w2n w)))
        ; SCTLR_EL2 := rec'SCTLRType ((31 >< 0) (SCTLR_EL2_ref.read_from asl'))
        ; SCTLR_EL3 := rec'SCTLRType ((31 >< 0) (SCTLR_EL3_ref.read_from asl'))
        ; SP_EL0 := SP_EL0_ref.read_from asl'
        ; SP_EL1 := SP_EL1_ref.read_from asl'
        ; SP_EL2 := SP_EL2_ref.read_from asl'
        ; SP_EL3 := SP_EL3_ref.read_from asl'
        ; TCR_EL2 := rec'TCR_EL2_EL3 ((31 >< 0) (TCR_EL2_ref.read_from asl'))
        ; TCR_EL3 := rec'TCR_EL2_EL3 (TCR_EL3_ref.read_from asl')
        ; branch_hint := if BranchTaken_ref.read_from asl' then SOME ARB else NONE
      |>` >>
  conj_tac >- simp[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq, IN_DEF] >>
  gen_tac >> simp[] >>
  gvs[state_rel_def, read_rel_def] >>
  gvs[interference_ok_def, arm8_asl_proj_def] >>
  simp[sctlr_rel_def, tcr_el2_3_rel_def, branch_hint_rel_def] >>
  rpt conj_tac
  >- (simp[rec'SCTLRType_def, reg'SCTLRType_def] >> blastLib.BBLAST_TAC)
  >- (simp[rec'SCTLRType_def, reg'SCTLRType_def] >> blastLib.BBLAST_TAC)
  >- (simp[rec'TCR_EL2_EL3_def, reg'TCR_EL2_EL3_def] >> blastLib.BBLAST_TAC)
  >- (simp[rec'TCR_EL2_EL3_def, reg'TCR_EL2_EL3_def] >> blastLib.BBLAST_TAC)
  >- rw[]
  >- gvs[reg_rel_def] >>
  `arm8_asl_mem_ok asl` by (
    gvs[arm8_asl_mem_ok_def, mem_rel_def] >> gen_tac >>
    first_x_assum $ qspec_then `w` assume_tac >> gvs[] >>
    goal_assum drule >> simp[]) >>
  `arm8_asl_mem_ok (env i asl)` by gvs[] >>
  `fun2set ($' (env i asl).memstate o w2n, m) =
    fun2set ($' asl.memstate o w2n, m)` by gvs[] >>
  last_x_assum kall_tac >>
  gvs[mem_rel_def, arm8_asl_mem_ok_def] >> gen_tac >>
  rpt $ first_x_assum $ qspec_then `w` assume_tac >> gvs[] >>
  irule_at Any EQ_REFL >> simp[] >>
  gvs[set_sepTheory.fun2set_eq, IN_DEF] >> rw[]
  >- (
    first_x_assum drule >> rw[] >> gvs[FLOOKUP_DEF] >>
    AP_TERM_TAC >> gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN] >> rw[LIST_EQ_REWRITE] >>
    rpt $ first_x_assum drule >> rw[sail2_valuesTheory.bitU_of_bool_def]
    )
  >- (gvs[FLOOKUP_DEF] >> simp[MAP_MAP_o, combinTheory.o_DEF])
QED

Theorem l3_asl_next:
  ∀l3 asl i n instr.
    state_rel l3 asl ∧ asl_sys_regs_ok asl ∧
    n < LENGTH (arm8_ast i) ∧
    Encode (EL n (arm8_ast i)) = ARM8 instr ∧
    l3.MEM l3.PC = (7 >< 0) instr ∧ l3.MEM (l3.PC + 1w) = (15 >< 8) instr ∧
    l3.MEM (l3.PC + 2w) = (23 >< 16) instr ∧ l3.MEM (l3.PC + 3w) = (31 >< 24) instr ∧
    arm8_ok l3 ∧ IS_SOME (NextStateARM8 l3)
  ⇒ state_rel (THE (NextStateARM8 l3)) (SND $ arm8_asl_next asl) ∧
    asl_sys_regs_ok (SND $ arm8_asl_next asl)
Proof
  rpt gen_tac >> strip_tac >> gvs[arm8_encode_def, NextStateARM8_def] >>
  every_case_tac >> gvs[] >>
  qspecl_then [`EL n (arm8_ast i)`,`i`] mp_tac l3_asl_arm8_ast >>
  simp[rich_listTheory.EL_MEM] >>
  simp[l3_models_asl_instr_def, l3_models_asl_def] >> strip_tac >> gvs[] >>
  qabbrev_tac `asl1 = asl with regstate := BranchTaken_ref.write_to F asl.regstate` >>
  `state_rel (l3 with branch_hint := NONE) asl1 ∧ asl_sys_regs_ok asl1` by (
    unabbrev_all_tac >> state_rel_tac[]) >>
  first_x_assum drule >> disch_then drule >>
  `Fetch (l3 with branch_hint := NONE) = (instr,l3 with branch_hint := NONE)` by (
    simp[Fetch_def, Mem_def] >>
    ntac 4 $ ntac 4 $ simp[Once state_transformerTheory.FOR_def] >>
    simp[state_transformerTheory.BIND_DEF] >>
    map_every (rewrite_tac o single) [
      GSYM APPEND_ASSOC, concat16, concat32, concat64] >>
    `aligned 2 l3.PC` by gvs[arm8_ok_def] >>
    simp[CheckAlignment_def, Aligned_def, Align] >> gvs[alignmentTheory.aligned_def] >>
    `¬BigEndian (l3 with branch_hint := NONE)` by gvs[BigEndian_def, arm8_ok_def] >>
    simp[] >> blastLib.BBLAST_TAC) >>
  gvs[Next_def, COND_RAND] >>
  CASE_TAC >> simp[] >> rename1 `res,asl2` >> CASE_TAC >> simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `state_rel l3'` >>
  qsuff_tac
    `arm8_asl_next asl =
      if BranchTaken_ref.read_from asl2.regstate then returnS () asl2
      else PC_set (PC_ref.read_from asl2.regstate + 4w) asl2`
  >- (
    strip_tac >> simp[] >> reverse conj_tac
    >- (
      simp[armv86aTheory.PC_set_def, armv86a_typesTheory.BranchTaken_ref_def] >>
      simp[returnS, seqS, asl_reg_rws, COND_RAND] >> rw[DISJ_EQ_IMP] >>
      gvs[asl_sys_regs_ok_def]
      ) >>
    `IS_SOME (l3'.branch_hint) = BranchTaken_ref.read_from asl2.regstate` by
      state_rel_tac[] >>
    rw[] >> gvs[returnS] >>
    gvs[armv86aTheory.PC_set_def, returnS, seqS, asl_reg_rws] >>
    state_rel_tac[]
    ) >>
  simp[arm8_asl_next_def] >>
  `write_regS BranchTaken_ref F asl = returnS () asl1 : unit res` by (
    unabbrev_all_tac >> simp[asl_reg_rws]) >>
  simp[Once seqS, returnS] >>
  `PC_ref.read_from asl1.regstate = l3.PC` by state_rel_tac[] >> simp[] >>
  `PC_read () asl1 = returnS l3.PC asl1` by (pop_assum mp_tac >> EVAL_TAC) >>
  simp[Once bindS, returnS] >>
  qspecl_then [`l3 with branch_hint := NONE`,`asl1`,`l3.PC`]
    mp_tac l3_asl_Mem_read0_4_AccType_IFETCH >> simp[] >>
  impl_tac >- gvs[arm8_ok_def, Aligned_def, Align, alignmentTheory.aligned_def] >>
  gvs[Fetch_def] >> strip_tac >> simp[Once bindS, returnS] >>
  qpat_x_assum `_ = (_,asl2)` mp_tac >>
  simp[Once seqS] >> CASE_TAC >> simp[] >> CASE_TAC >> simp[] >> strip_tac >>
  ntac 2 $ simp[Once seqS] >>
  `read_regS BranchTaken_ref asl2 : bool res =
    returnS (BranchTaken_ref.read_from asl2.regstate) asl2` by EVAL_TAC >>
  simp[bindS, returnS, COND_RATOR] >> rw[] >> EVAL_TAC
QED

Theorem l3_asl_target:
  ∀l3 asl. state_rel l3 asl ⇒
    arm8_asl_target.get_byte asl = l3.MEM ∧
    PC_ref.read_from asl.regstate = l3.PC ∧
    arm8_asl_target.get_pc asl = l3.PC
Proof
  reverse $ rw[FUN_EQ_THM] >> simp[arm8_asl_target_def]
  >- state_rel_tac[] >- state_rel_tac[] >>
  `mem_rel l3.MEM asl.memstate asl.tagstate` by gvs[state_rel_def] >>
  gvs[mem_rel] >>
  first_x_assum $ qspec_then `x` assume_tac >> gvs[FLOOKUP_DEF] >>
  simp[MAP_MAP_o, combinTheory.o_DEF]
QED


(********** target_ok **********)

Theorem arm8_asl_target_ok:
  target_ok arm8_asl_target
Proof
  `target_ok arm8_target` by
    metis_tac[arm8_encoder_correct, encoder_correct_def] >>
  simp[target_ok_def] >> conj_tac
  >- gvs[target_ok_def, arm8_asl_target_def, arm8_target_def] >>
  rpt gen_tac >> strip_tac >> reverse conj_tac
  >- (
    gvs[arm8_asl_target_def, arm8_asl_target_def, arm8_asl_proj_def] >>
    simp[arm8_asl_ok_def] >> rw[] >> gvs[set_sepTheory.fun2set_eq]
    ) >>
  gvs[target_state_rel_def] >>
  gvs[arm8_asl_target_def, arm8_asl_proj_def, arm8_config_def] >>
  eq_tac >> strip_tac >> simp[] >>
  gvs[arm8_asl_ok_def] >> rw[] >>
  first_x_assum drule >> disch_then $ assume_tac o GSYM >> simp[] >>
  gvs[set_sepTheory.fun2set_eq]
QED


(********** encoder_correct **********)

(***** some simple tactics adapted from arm8_targetProofLib *****)
val encode = gvs enc_rwts

val asserts = gvs[
  asmPropsTheory.asserts_eval, asmPropsTheory.asserts2_eval
  ];

val asm = gvs asm_rwts;

val next_l3_tac = next_state_tac0 true List.last filter_reg_31;

fun l3_state_tac thms =
  arm8_fs ([
    interference_ok_def, arm8_proj_def,
    asmPropsTheory.sym_target_state_rel, arm8_target_def,
    arm8_config, asmPropsTheory.all_pcs, arm8_ok_def, lem30,
    set_sepTheory.fun2set_eq
    ] @ thms) >>
  rewrite_tac[combinTheory.APPLY_UPDATE_THM, alignmentTheory.aligned_numeric] >>
  arm8_fs[] >> rw[] >> arm8_rfs[];

fun interference q (asl,g) =
  let val ctxt = free_varsl (g::asl)
      val tm = Parse.parse_in_context ctxt q
  in
    (qpat_x_assum `interference_ok ^tm (arm8_proj _)` $ assume_tac o
      SIMP_RULE (srw_ss()) [interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq])
  end (asl,g);

val shift_cases_tac =
  Cases_on `s` >| [
    qspecl_then [`n2w ((64 - n1) MOD 64)`, `n2w ((64 - n1) MOD 64) + 63w`]
      strip_assume_tac DecodeBitMasks_SOME >>
    qabbrev_tac `r: word6 = n2w ((64 - n1) MOD 64)` >> qabbrev_tac `q = r + 63w` >>
    `¬(w2n q = 63 ∧ r ≠ 0w)` by (
      Cases_on `r = 0w` >> simp[] >>
      irule $ WORD_DECIDE ``a <> 63w ==> w2n (a: word6) <> 63`` >>
      qunabbrev_tac `q` >> blastLib.FULL_BBLAST_TAC)
  , qspecl_then [`n2w n1`, `63w`] strip_assume_tac DecodeBitMasks_SOME
  , qspecl_then [`n2w n1`, `63w`] strip_assume_tac DecodeBitMasks_SOME
  , all_tac
  ]

val print_tac = asmLib.print_tac "encoder_correct"
val ext12 = ``(11 >< 0) : word64 -> word12``

Theorem arm8_asl_encoder_correct:
  encoder_correct arm8_asl_target
Proof
  simp[encoder_correct_def, arm8_asl_target_ok] >>
  qpat_abbrev_tac `srel = target_state_rel _` >>
  qpat_abbrev_tac `gb = arm8_asl_target.get_byte` >>
  rw[arm8_asl_target_def, asmSemTheory.asm_step_def, arm8_config] >>
  unabbrev_all_tac >> rename1 `target_state_rel _ _ asl1` >>
  qexists_tac `LENGTH (arm8_enc i) DIV 4 - 1` >>
  gen_tac >> strip_tac >>
  drule exists_arm8_ok >> strip_tac >>
  `asl_sys_regs_ok asl1` by
    gvs[target_state_rel_def, arm8_asl_target_def, arm8_asl_ok_def] >>
  drule l3_asl_next >> simp[] >>
  disch_then $ qspecl_then [`i`,`0`] mp_tac >>
  Cases_on `i`
  >- ( (* Inst *)
    Cases_on `i'`
    >- ( (* Skip *)
      print_tac "Inst - Skip" >>
      encode >> asserts >> next_l3_tac `l3` >> strip_tac >>
      irule_at Any $ iffLR l3_asl_target_state_rel >>
      drule_all l3_asl_interference_ok >> strip_tac >>
      pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
      conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def] >>
      imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[]
      )
    >- ( (* Const *)
      print_tac "Inst - Const" >>
      reverse $ Cases_on `arm8_enc_mov_imm c`
      >- (
        PairCases_on `x` >> encode >> asserts >> next_l3_tac `l3` >> strip_tac >>
        imp_res_tac lem27 >> pop_assum $ SUBST_ALL_TAC o GSYM >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def] >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[]
        ) >>
      reverse $ Cases_on `arm8_enc_mov_imm (¬c)`
      >- (
        PairCases_on `x` >> encode >> asserts >> next_l3_tac `l3` >> strip_tac >>
        imp_res_tac lem27 >> pop_assum $ SUBST_ALL_TAC o GSYM >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def] >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[]
        ) >>
      reverse $ Cases_on `EncodeBitMask c`
      >- (
        PairCases_on `x` >> encode >> asserts >> next_l3_tac `l3` >> strip_tac >>
        imp_res_tac Decode_EncodeBitMask >> gvs[] >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def] >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[]
        ) >>
      encode >> asserts >>
      split_bytes_in_memory_tac 4 >> next_l3_tac `l3` >> strip_tac >>
      qcollapse_tac `(15 >< 0) c` >>
      drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
      pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
      >- (
        simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
        goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
        simp[alignmentTheory.aligned_numeric]
        ) >>
      drule l3_asl_next >>
      disch_then $ qspecl_then [`Inst (Const n c)`,`1`] mp_tac >> encode >>
      split_bytes_in_memory_tac 4 >>
      interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
      `∀a. a ∈ s1.mem_domain ⇒
        (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
        gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
      next_state_tac0 false (fn l => List.nth (l,1))
        filter_reg_31 `l3_env 0n (THE $ NextStateARM8 l3)` >>
      impl_tac
      >- (
        gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
        simp[alignmentTheory.aligned_numeric]
        ) >>
      strip_tac >> qcollapse_tac `(31 >< 16) c` >>
      drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
      pop_assum $ qspec_then `1` assume_tac >>
      drule l3_asl_next >>
      disch_then $ qspecl_then [`Inst (Const n c)`,`2`] mp_tac >> encode >>
      split_bytes_in_memory_tac 4 >>
      interference `l3_env'` >> imp_res_tac $ Q.SPEC `8w` bytes_in_memory_thm2 >>
      qmatch_goalsub_abbrev_tac `l3_env' _ l3_state` >>
      `∀a. a ∈ s1.mem_domain ⇒ (l3_env' 1 l3_state).MEM a = l3_state.MEM a` by
        gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
      unabbrev_all_tac >>
      imp_res_tac interference_ok_def >> gvs[arm8_proj_def, arm8_ok_def] >>
      simp[alignmentTheory.aligned_numeric, GSYM AND_IMP_INTRO] >>
      impl_tac >- gvs[arm8_asl_proj_def] >>
      next_state_tac0 false (fn l => List.nth (l,1)) filter_reg_31
        `l3_env' 1n $ THE $ NextStateARM8 $ l3_env 0n $ THE $ NextStateARM8 l3` >>
      qcollapse_tac `(47 >< 32) c` >> strip_tac >> gvs[] >>
      drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
      pop_assum $ qspec_then `2` assume_tac >>
      drule l3_asl_next >>
      disch_then $ qspecl_then [`Inst (Const n c)`,`3`] mp_tac >> encode >>
      interference `l3_env''` >>
      imp_res_tac $ Q.SPEC `12w` bytes_in_memory_thm2 >>
      qmatch_goalsub_abbrev_tac `l3_env'' _ l3_state` >>
      `∀a. a ∈ s1.mem_domain ⇒ (l3_env' 1 l3_state).MEM a = l3_state.MEM a` by
        gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
      unabbrev_all_tac >>
      imp_res_tac interference_ok_def >>
      gvs[arm8_proj_def, arm8_ok_def] >>
      simp[alignmentTheory.aligned_numeric, GSYM AND_IMP_INTRO] >>
      impl_tac >- gvs[arm8_asl_proj_def] >>
      next_state_tac0 false (fn l => List.nth (l,0)) filter_reg_31
        `l3_env'' 2n $ THE $ NextStateARM8 $
          l3_env' 1n $ THE $ NextStateARM8 $ l3_env 0n $ THE $ NextStateARM8 l3` >>
      qcollapse_tac `(63 >< 48) c` >> strip_tac >> gvs[] >>
      imp_res_tac l3_asl_target >> simp[] >>
      irule_at Any $ iffLR l3_asl_target_state_rel >>
      drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
      pop_assum $ qspec_then `3` assume_tac >> goal_assum drule >>
      rename1 `target_state_rel _ _ (l3_env3 _ _)` >>
      interference `l3_env3` >> simp[] >>
      gvs[interference_ok_def, arm8_asl_proj_def] >>
      simp[arm8_asl_ok, PULL_EXISTS] >>
      rpt $ goal_assum $ drule_at Any >> simp[arm8_ok_def] >>
      l3_state_tac[] >> blastLib.BBLAST_TAC
      )
    >- ( (* Arith *)
      Cases_on `a`
      >- ( (* Binop *)
        print_tac "Inst - Arith - Binop" >>
        Cases_on `r` >| [
          Cases_on `b`,
          Cases_on `b = Xor ∧ c = -1w` >| [all_tac, Cases_on `b` >> gvs[]]
          ] >>
        encode >> asserts >>
        next_l3_tac `l3` >> strip_tac >>
        imp_res_tac Decode_EncodeBitMask >> gvs[] >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[] >>
        DEP_REWRITE_TAC[SIMP_RULE (srw_ss()) [] lem23] >> simp[]
        )
      >- ( (* Shift *)
        print_tac "Inst - Arith - Shift" >>
        shift_cases_tac >> encode >> asserts >>
        qspec_then `r` assume_tac w2n_lt >> qspec_then `q` assume_tac w2n_lt >> gvs[] >>
        unabbrev_all_tac >> gvs[]
        >- (
          next_l3_tac `l3` >> strip_tac >>
          first_x_assum $ qspecl_then [`tmask`,`wmask`] mp_tac >> impl_tac
          >- (
            qpat_x_assum `_ = SOME (_,_)` $ assume_tac o GSYM >> simp[] >>
            AP_TERM_TAC >> simp[] >> blastLib.BBLAST_TAC
            ) >>
          strip_tac >> gvs[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >>
          pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
          (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
          imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[] >>
          DEP_REWRITE_TAC [lsl |> SIMP_RULE (srw_ss()) [markerTheory.Abbrev_def]] >>
          simp[]
          ) >>
        next_l3_tac `l3` >> strip_tac >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[lsr, asr, ror]
        >- (
          drule_at (Pos last) lsr >> rw[] >>
          qsuff_tac `n1 = 0` >- rw[] >> intLib.ARITH_TAC
          )
        >- (drule_all asr2 >> simp[])
        )
      >- ( (* Div *)
        print_tac "Inst - Arith - Div" >>
        encode >> asserts >>
        next_l3_tac `l3` >> strip_tac >>
        imp_res_tac Decode_EncodeBitMask >> gvs[] >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[]
        )
      >- ( (* LongMul *)
        print_tac "Inst - Arith - LongMul" >>
        encode >> asserts >>
        split_bytes_in_memory_tac 4 >> next_l3_tac `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`Inst (Arith (LongMul n n0 n1 n2))`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        next_state_tac0 false (fn l => List.nth (l,0))
          filter_reg_31 `l3_env 0n (THE $ NextStateARM8 l3)` >>
        impl_tac
        >- (
          gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
        interference `l3_env'` >> simp[] >> conj_tac
        >- gvs[interference_ok_def, arm8_asl_proj_def] >>
        simp[GSYM word_mul_def, mul_long, ExtendWord_def] >>
        l3_state_tac[]
        )
      >- encode (* LongDiv *)
      >- ( (* AddCarry *)
        print_tac "Inst - Arith - AddCarry" >>
        encode >> asserts >>
        split_bytes_in_memory_tac 4 >>
        next_state_tac0 true List.last filter_vacuous `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`Inst (Arith (AddCarry n n0 n1 n2))`,`1`] mp_tac >>
        encode >>
        split_bytes_in_memory_tac 4 >>
        interference `l3_env` >>
        drule_all $ Q.SPEC `4w` bytes_in_memory_thm2 >> strip_tac >> gvs[] >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        next_state_tac0 false (fn l => List.nth (l,1))
          filter_reg_31 `l3_env 0n (THE $ NextStateARM8 l3)` >>
        impl_tac
        >- (
          gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        strip_tac >> drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `1` assume_tac >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`Inst (Arith (AddCarry n n0 n1 n2))`,`2`] mp_tac >>
        encode >>
        split_bytes_in_memory_tac 4 >>
        interference `l3_env'` >>
        drule_all $ Q.SPEC `8w` bytes_in_memory_thm2 >> strip_tac >> gvs[] >>
        qmatch_goalsub_abbrev_tac `l3_env' _ l3_state` >>
        `∀a. a ∈ s1.mem_domain ⇒ (l3_env' 1 l3_state).MEM a = l3_state.MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        unabbrev_all_tac >>
        imp_res_tac interference_ok_def >> gvs[arm8_proj_def, arm8_ok_def] >>
        simp[alignmentTheory.aligned_numeric, GSYM AND_IMP_INTRO] >>
        impl_tac >- gvs[arm8_asl_proj_def] >>
        next_state_tac0 false (fn l => List.nth (l,1)) filter_reg_31
          `l3_env' 1n $ THE $ NextStateARM8 $ l3_env 0n $ THE $ NextStateARM8 l3` >>
        strip_tac >> gvs[] >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `2` assume_tac >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`Inst (Arith (AddCarry n n0 n1 n2))`,`3`] mp_tac >>
        encode >>
        split_bytes_in_memory_tac 4 >>
        interference `l3_env''` >>
        drule_all $ Q.SPEC `12w` bytes_in_memory_thm2 >> strip_tac >> gvs[] >>
        qmatch_goalsub_abbrev_tac `l3_env'' _ l3_state` >>
        `∀a. a ∈ s1.mem_domain ⇒ (l3_env'' 1 l3_state).MEM a = l3_state.MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        unabbrev_all_tac >>
        imp_res_tac interference_ok_def >> gvs[arm8_proj_def, arm8_ok_def] >>
        simp[alignmentTheory.aligned_numeric, GSYM AND_IMP_INTRO] >>
        impl_tac >- gvs[arm8_asl_proj_def] >>
        next_state_tac0 false (fn l => List.nth (l,1)) filter_reg_31
          `l3_env'' 2n $ THE $ NextStateARM8 $
            l3_env' 1n $ THE $ NextStateARM8 $ l3_env 0n $ THE $ NextStateARM8 l3` >>
        strip_tac >> gvs[] >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `3` assume_tac >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`Inst (Arith (AddCarry n n0 n1 n2))`,`4`] mp_tac >>
        encode >>
        interference `l3_env'³'` >> gvs[] >>
        drule_all $ Q.SPEC `16w` bytes_in_memory_thm2 >> strip_tac >> gvs[] >>
        qmatch_goalsub_abbrev_tac `l3_env'³' _ l3_state` >>
        `∀a. a ∈ s1.mem_domain ⇒ (l3_env'³' 1 l3_state).MEM a = l3_state.MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        unabbrev_all_tac >>
        imp_res_tac interference_ok_def >> gvs[arm8_proj_def, arm8_ok_def] >>
        simp[alignmentTheory.aligned_numeric, GSYM AND_IMP_INTRO] >>
        impl_tac >- gvs[arm8_asl_proj_def] >>
        next_state_tac0 false (fn l => List.nth (l,0)) filter_reg_31
          `l3_env'³' 3n $ THE $ NextStateARM8 $ l3_env'' 2n $ THE $ NextStateARM8 $
            l3_env' 1n $ THE $ NextStateARM8 $ l3_env 0n $ THE $ NextStateARM8 l3` >>
        strip_tac >> gvs[] >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `4` assume_tac >>
        imp_res_tac l3_asl_target >> simp[] >>
        irule_at Any $ iffLR l3_asl_target_state_rel >> goal_assum drule >>
        interference `l3_env'⁴'` >> simp[] >>
        gvs[interference_ok_def, arm8_asl_proj_def] >>
        simp[arm8_asl_ok, PULL_EXISTS] >>
        rpt $ goal_assum $ drule_at Any >> simp[arm8_ok_def] >>
        l3_state_tac[] >>
        simp[add_with_carry_def, ConditionTest_def] >>
        Cases_on `l3.REG (n2w i) = 0w` >> gvs[]
        )
      >- ( (* AddOverflow *)
        print_tac "Inst - Arith - AddOverflow" >>
        encode >> asserts >>
        split_bytes_in_memory_tac 4 >> next_l3_tac `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`Inst (Arith (AddOverflow n n0 n1 n2))`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        next_state_tac0 false (fn l => List.nth (l,0))
          filter_reg_31 `l3_env 0n (THE $ NextStateARM8 l3)` >>
        impl_tac
        >- (
          gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
        interference `l3_env'` >> simp[] >> conj_tac
        >- gvs[interference_ok_def, arm8_asl_proj_def] >>
        simp[integer_wordTheory.overflow_add] >> l3_state_tac[]
        )
      >- ( (* SubOverflow *)
        print_tac "Inst - Arith - SubOverflow" >>
        encode >> asserts >>
        split_bytes_in_memory_tac 4 >> next_l3_tac `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`Inst (Arith (SubOverflow n n0 n1 n2))`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        next_state_tac0 false (fn l => List.nth (l,0))
          filter_reg_31 `l3_env 0n (THE $ NextStateARM8 l3)` >>
        impl_tac
        >- (
          gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
        interference `l3_env'` >> simp[] >> conj_tac
        >- gvs[interference_ok_def, arm8_asl_proj_def] >>
        gvs[integer_wordTheory.sub_overflow] >> l3_state_tac[] >>
        ntac 3 $ pop_assum mp_tac >>
        rewrite_tac[GSYM $ SIMP_CONV (srw_ss()) [] ``-w:word64``] >>
        rewrite_tac[GSYM word_sub_def] >>
        rewrite_tac[integer_wordTheory.sub_overflow] >> gvs[]
        )
      )
    >- ( (* Mem *)
      print_tac "Inst - Mem" >>
      qabbrev_tac `instr = Mem m n a` >>
      Cases_on `a` >> Cases_on `m` >| [
        Cases_on `c = sw2sw ((8 >< 0) c : word9)` >| [
          Cases_on `¬word_msb c ∧ c = w2w (^ext12 (c >>> 3)) << 3`,
          Cases_on `word_msb c` >| [
            all_tac,
            Cases_on `c = w2w (^ext12 (c >>> 3)) << 3`
            ]
          ]
      , Cases_on `~word_msb c /\ (c = w2w (^ext12 c))`
      , Cases_on `c = sw2sw ((8 >< 0) c : word9)` >| [
          Cases_on `¬word_msb c ∧ c = w2w (^ext12 (c >>> 2)) << 2`,
          Cases_on `word_msb c` >| [
            all_tac,
            Cases_on `c = w2w (^ext12 (c >>> 2)) << 2`
            ]
          ]
      , Cases_on `c = sw2sw ((8 >< 0) c : word9)` >| [
          Cases_on `¬word_msb c ∧ c = w2w (^ext12 (c >>> 3)) << 3`,
          Cases_on `word_msb c` >| [
            all_tac, Cases_on `c = w2w (^ext12 (c >>> 3)) << 3`
            ]
        ]
      , Cases_on `~word_msb c /\ (c = w2w (^ext12 c))`
      , Cases_on `c = sw2sw ((8 >< 0) c : word9)` >| [
          Cases_on `¬word_msb c ∧ c = w2w (^ext12 (c >>> 2)) << 2`,
          Cases_on `word_msb c` >| [
            all_tac,
            Cases_on `c = w2w (^ext12 (c >>> 2)) << 2`
            ]
          ]
      ] >>
      rfs[] >> fs[lem7, lem7b, lem31, lem35]
      >- (
        unabbrev_all_tac >> encode >> asserts >>
        `aligned 3 (c + l3.REG (n2w n'))` by imp_res_tac lem14 >>
        next_l3_tac `l3` >> strip_tac >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[] >>
        simp[mem_dword_def, ExtendWord_def] >> simp[SF wordsLib.WORD_EXTRACT_ss]
        )
      >- (
        unabbrev_all_tac >> encode >> asserts >>
        `aligned 3 (c + l3.REG (n2w n'))` by imp_res_tac lem14 >>
        next_l3_tac `l3` >> strip_tac >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[] >>
        simp[mem_dword_def, ExtendWord_def] >> simp[SF wordsLib.WORD_EXTRACT_ss]
        )
      >- (
        unabbrev_all_tac >> encode >> asserts >>
        `aligned 3 (c + l3.REG (n2w n'))` by imp_res_tac lem14 >>
        next_l3_tac `l3` >> strip_tac >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[] >>
        simp[mem_dword_def, ExtendWord_def] >> simp[SF wordsLib.WORD_EXTRACT_ss]
        )
      >- ( (* Mem Load n (Addr n' c) *)
        unabbrev_all_tac >> encode >>
        drule_all lem31 >> strip_tac >> gvs[] >> asserts >>
        `aligned 3 (c + l3.REG (n2w n'))` by imp_res_tac lem14 >>
        split_bytes_in_memory_tac 4 >> next_l3_tac `l3` >> strip_tac >>
        qmatch_asmsub_abbrev_tac `c * foo` >>
        `foo = -1w` by (unabbrev_all_tac >> blastLib.BBLAST_TAC) >>
        pop_assum SUBST_ALL_TAC >> pop_assum kall_tac >>
        qmatch_asmsub_abbrev_tac `v2w foo` >>
        `v2w foo = (11 >< 0) (-1w * c - 0x100w)` by (
          qpat_x_assum `c ≤ _` mp_tac >> qpat_x_assum `_ ≤ c` mp_tac >>
          unabbrev_all_tac >> blastLib.BBLAST_TAC) >>
        pop_assum SUBST_ALL_TAC >> pop_assum kall_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`Inst (Mem Load n (Addr n' c))`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        next_state_tac0 true (fn l => List.nth (l,0))
          filter_reg_31 `l3_env 0n (THE $ NextStateARM8 l3)` >>
        drule_all lem33 >> simp[] >> disch_then SUBST_ALL_TAC >>
        pop_assum mp_tac >> impl_tac >- simp[alignmentTheory.aligned_numeric] >>
        strip_tac >> gvs[] >> impl_tac
        >- (
          gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
        interference `l3_env'` >> simp[] >> conj_tac
        >- gvs[interference_ok_def, arm8_asl_proj_def] >>
        l3_state_tac[] >>
        simp[mem_dword_def, ExtendWord_def] >> simp[SF wordsLib.WORD_EXTRACT_ss]
        )
      >- (
        unabbrev_all_tac >> encode >> asserts >>
        `aligned 3 (c + l3.REG (n2w n'))` by imp_res_tac lem14 >>
        next_l3_tac `l3` >> strip_tac >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[] >>
        simp[mem_dword_def, ExtendWord_def] >> simp[SF wordsLib.WORD_EXTRACT_ss]
        )
      >- ( (* Mem Load n (Addr n' c) *)
        unabbrev_all_tac >> encode >>
        drule_all lem35 >> strip_tac >> gvs[] >> asserts >>
        `aligned 3 (c + l3.REG (n2w n'))` by imp_res_tac lem14 >>
        split_bytes_in_memory_tac 4 >> next_l3_tac `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`Inst (Mem Load n (Addr n' c))`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        next_state_tac0 false (fn l => List.nth (l,0))
          filter_reg_31 `l3_env 0n (THE $ NextStateARM8 l3)` >>
        impl_tac
        >- (
          gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
        interference `l3_env'` >> simp[] >> conj_tac
        >- gvs[interference_ok_def, arm8_asl_proj_def] >>
        l3_state_tac[] >>
        simp[mem_dword_def, ExtendWord_def] >> simp[SF wordsLib.WORD_EXTRACT_ss]
        )
      >- (
        unabbrev_all_tac >> encode >> asserts >>
        next_l3_tac `l3` >> strip_tac >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[] >>
        simp[mem_dword_def, ExtendWord_def] >> simp[SF wordsLib.WORD_EXTRACT_ss]
        )
      >- (
        unabbrev_all_tac >> encode >> asserts >>
        next_l3_tac `l3` >> strip_tac >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[] >>
        simp[mem_dword_def, ExtendWord_def] >> simp[SF wordsLib.WORD_EXTRACT_ss]
        )
      >- (
        unabbrev_all_tac >> encode >> asserts >>
        next_l3_tac `l3` >> strip_tac >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[] >>
        simp[mem_dword_def, ExtendWord_def] >> simp[SF wordsLib.WORD_EXTRACT_ss]
        )
      >- (
        unabbrev_all_tac >> encode >> asserts >>
        `aligned 2 (c + l3.REG (n2w n'))` by imp_res_tac lem14b >>
        next_l3_tac `l3` >> strip_tac >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[] >>
        simp[mem_word_def, ExtendWord_def] >> simp[SF wordsLib.WORD_EXTRACT_ss]
        )
      >- (
        unabbrev_all_tac >> encode >> asserts >>
        `aligned 2 (c + l3.REG (n2w n'))` by imp_res_tac lem14b >>
        next_l3_tac `l3` >> strip_tac >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[] >>
        simp[mem_word_def, ExtendWord_def] >> simp[SF wordsLib.WORD_EXTRACT_ss]
        )
      >- (
        unabbrev_all_tac >> encode >> asserts >>
        `aligned 2 (c + l3.REG (n2w n'))` by imp_res_tac lem14b >>
        next_l3_tac `l3` >> strip_tac >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[] >>
        simp[mem_word_def, ExtendWord_def] >> simp[SF wordsLib.WORD_EXTRACT_ss]
        )
      >- (
        unabbrev_all_tac >> encode >>
        drule_all lem31 >> strip_tac >> gvs[] >> asserts >>
        `aligned 2 (c + l3.REG (n2w n'))` by imp_res_tac lem14b >>
        split_bytes_in_memory_tac 4 >> next_l3_tac `l3` >> strip_tac >>
        qmatch_asmsub_abbrev_tac `c * foo` >>
        `foo = -1w` by (unabbrev_all_tac >> blastLib.BBLAST_TAC) >>
        pop_assum SUBST_ALL_TAC >> pop_assum kall_tac >>
        qmatch_asmsub_abbrev_tac `v2w foo` >>
        `v2w foo = (11 >< 0) (-1w * c - 0x100w)` by (
          qpat_x_assum `c ≤ _` mp_tac >> qpat_x_assum `_ ≤ c` mp_tac >>
          unabbrev_all_tac >> blastLib.BBLAST_TAC) >>
        pop_assum SUBST_ALL_TAC >> pop_assum kall_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`Inst (Mem Load32 n (Addr n' c))`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        next_state_tac0 true (fn l => List.nth (l,0))
          filter_reg_31 `l3_env 0n (THE $ NextStateARM8 l3)` >>
        drule_all lem33 >> simp[] >> disch_then SUBST_ALL_TAC >>
        pop_assum mp_tac >> impl_tac >- simp[alignmentTheory.aligned_numeric] >>
        strip_tac >> gvs[] >> impl_tac
        >- (
          gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
        interference `l3_env'` >> simp[] >> conj_tac
        >- gvs[interference_ok_def, arm8_asl_proj_def] >>
        l3_state_tac[] >>
        simp[mem_word_def, ExtendWord_def] >> simp[SF wordsLib.WORD_EXTRACT_ss]
        )
      >- (
        unabbrev_all_tac >> encode >> asserts >>
        `aligned 2 (c + l3.REG (n2w n'))` by imp_res_tac lem14b >>
        next_l3_tac `l3` >> strip_tac >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[] >>
        simp[mem_word_def, ExtendWord_def] >> simp[SF wordsLib.WORD_EXTRACT_ss]
        )
      >- (
        unabbrev_all_tac >> encode >>
        drule_all lem35 >> strip_tac >> gvs[] >> asserts >>
        `aligned 2 (c + l3.REG (n2w n'))` by imp_res_tac lem14b >>
        split_bytes_in_memory_tac 4 >> next_l3_tac `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`Inst (Mem Load32 n (Addr n' c))`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        next_state_tac0 false (fn l => List.nth (l,0))
          filter_reg_31 `l3_env 0n (THE $ NextStateARM8 l3)` >>
        impl_tac
        >- (
          gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
        interference `l3_env'` >> simp[] >> conj_tac
        >- gvs[interference_ok_def, arm8_asl_proj_def] >>
        l3_state_tac[] >>
        simp[mem_word_def, ExtendWord_def] >> simp[SF wordsLib.WORD_EXTRACT_ss]
        )
      >- (
        unabbrev_all_tac >> encode >> asserts >>
        imp_res_tac bytes_in_memory_thm >> gvs[] >>
        next_state_tac0 false (fn l => List.nth (l,0)) filter_reg_31 `l3` >>
        pop_assum mp_tac >> impl_tac
        >- gvs[target_state_rel_def, arm8_target_def, arm8_config_def] >>
        ntac 2 strip_tac >> gvs[] >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[] >> gvs[] >>
        pop_assum mp_tac >> blastLib.BBLAST_TAC
        )
      >- (
        unabbrev_all_tac >> encode >> asserts >>
        imp_res_tac bytes_in_memory_thm >> gvs[] >>
        next_state_tac0 false (fn l => List.nth (l,0)) filter_reg_31 `l3` >>
        pop_assum mp_tac >> impl_tac
        >- gvs[target_state_rel_def, arm8_target_def, arm8_config_def] >>
        ntac 2 strip_tac >> gvs[] >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[] >> gvs[] >>
        pop_assum mp_tac >> blastLib.BBLAST_TAC
        )
      >- (
        unabbrev_all_tac >> encode >> asserts >>
        imp_res_tac bytes_in_memory_thm >> gvs[] >>
        next_state_tac0 false (fn l => List.nth (l,0)) filter_reg_31 `l3` >>
        pop_assum mp_tac >> impl_tac
        >- gvs[target_state_rel_def, arm8_target_def, arm8_config_def] >>
        ntac 2 strip_tac >> gvs[] >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[] >> gvs[] >>
        pop_assum mp_tac >> blastLib.BBLAST_TAC
        )
      >- ( (* Mem Store n (Addr n' c) *)
        unabbrev_all_tac >> encode >>
        drule_all lem31 >> strip_tac >> gvs[] >> asserts >>
        `aligned 3 (c + l3.REG (n2w n'))` by imp_res_tac lem14 >>
        split_bytes_in_memory_tac 4 >> next_l3_tac `l3` >> strip_tac >>
        qmatch_asmsub_abbrev_tac `c * foo` >>
        `foo = -1w` by (unabbrev_all_tac >> blastLib.BBLAST_TAC) >>
        pop_assum SUBST_ALL_TAC >> pop_assum kall_tac >>
        qmatch_asmsub_abbrev_tac `v2w foo` >>
        `v2w foo = (11 >< 0) (-1w * c - 0x100w)` by (
          qpat_x_assum `c ≤ _` mp_tac >> qpat_x_assum `_ ≤ c` mp_tac >>
          unabbrev_all_tac >> blastLib.BBLAST_TAC) >>
        pop_assum SUBST_ALL_TAC >> pop_assum kall_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`Inst (Mem Store n (Addr n' c))`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        next_state_tac0 true (fn l => List.nth (l,0))
          filter_reg_31 `l3_env 0n (THE $ NextStateARM8 l3)` >>
        drule_all lem33 >> simp[] >> disch_then SUBST_ALL_TAC >>
        pop_assum mp_tac >> impl_tac >- simp[alignmentTheory.aligned_numeric] >>
        strip_tac >> gvs[] >> impl_tac
        >- (
          gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
        interference `l3_env'` >> simp[] >> conj_tac
        >- gvs[interference_ok_def, arm8_asl_proj_def] >>
        l3_state_tac[] >> gvs[] >>
        pop_assum mp_tac >> blastLib.BBLAST_TAC
        )
      >- (
        unabbrev_all_tac >> encode >> asserts >>
        imp_res_tac bytes_in_memory_thm >> gvs[] >>
        next_state_tac0 false (fn l => List.nth (l,0)) filter_reg_31 `l3` >>
        pop_assum mp_tac >> impl_tac
        >- gvs[target_state_rel_def, arm8_target_def, arm8_config_def] >>
        ntac 2 strip_tac >> gvs[] >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[] >> gvs[] >>
        pop_assum mp_tac >> blastLib.BBLAST_TAC
        )
      >- ( (* Mem Store n (Addr n' c) *)
        unabbrev_all_tac >> encode >>
        drule_all lem35 >> strip_tac >> gvs[] >> asserts >>
        `aligned 3 (c + l3.REG (n2w n'))` by imp_res_tac lem14 >>
        split_bytes_in_memory_tac 4 >> next_l3_tac `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`Inst (Mem Store n (Addr n' c))`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        next_state_tac0 false (fn l => List.nth (l,0))
          filter_reg_31 `l3_env 0n (THE $ NextStateARM8 l3)` >>
        impl_tac
        >- (
          gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
        interference `l3_env'` >> simp[] >> conj_tac
        >- gvs[interference_ok_def, arm8_asl_proj_def] >>
        l3_state_tac[] >>
        simp[mem_dword_def, ExtendWord_def] >> simp[SF wordsLib.WORD_EXTRACT_ss] >>
        gvs[] >> pop_assum mp_tac >> blastLib.BBLAST_TAC
        )
      >- (
        unabbrev_all_tac >> encode >> asserts >>
        next_l3_tac `l3` >> strip_tac >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[] >>
        simp[mem_dword_def, ExtendWord_def] >> simp[SF wordsLib.WORD_EXTRACT_ss]
        )
      >- (
        unabbrev_all_tac >> encode >> asserts >>
        next_l3_tac `l3` >> strip_tac >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[] >>
        simp[mem_dword_def, ExtendWord_def] >> simp[SF wordsLib.WORD_EXTRACT_ss]
        )
      >- (
        unabbrev_all_tac >> encode >> asserts >>
        next_l3_tac `l3` >> strip_tac >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[] >>
        simp[mem_dword_def, ExtendWord_def] >> simp[SF wordsLib.WORD_EXTRACT_ss]
        )
      >- (
        unabbrev_all_tac >> encode >> asserts >>
        imp_res_tac bytes_in_memory_thm >> gvs[] >>
        next_state_tac0 false (fn l => List.nth (l,0)) filter_reg_31 `l3` >>
        pop_assum mp_tac >> impl_tac
        >- gvs[target_state_rel_def, arm8_target_def, arm8_config_def] >>
        ntac 2 strip_tac >> gvs[] >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[] >> gvs[] >>
        pop_assum mp_tac >> blastLib.BBLAST_TAC
        )
      >- (
        unabbrev_all_tac >> encode >> asserts >>
        imp_res_tac bytes_in_memory_thm >> gvs[] >>
        next_state_tac0 false (fn l => List.nth (l,0)) filter_reg_31 `l3` >>
        pop_assum mp_tac >> impl_tac
        >- gvs[target_state_rel_def, arm8_target_def, arm8_config_def] >>
        ntac 2 strip_tac >> gvs[] >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[] >> gvs[] >>
        pop_assum mp_tac >> blastLib.BBLAST_TAC
        )
      >- (
        unabbrev_all_tac >> encode >> asserts >>
        imp_res_tac bytes_in_memory_thm >> gvs[] >>
        next_state_tac0 false (fn l => List.nth (l,0)) filter_reg_31 `l3` >>
        pop_assum mp_tac >> impl_tac
        >- gvs[target_state_rel_def, arm8_target_def, arm8_config_def] >>
        ntac 2 strip_tac >> gvs[] >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[] >> gvs[] >>
        pop_assum mp_tac >> blastLib.BBLAST_TAC
        )
      >- ( (* Mem Store n (Addr n' c) *)
        unabbrev_all_tac >> encode >>
        drule_all lem31 >> strip_tac >> gvs[] >> asserts >>
        `aligned 2 (c + l3.REG (n2w n'))` by imp_res_tac lem14b >>
        split_bytes_in_memory_tac 4 >> next_l3_tac `l3` >> strip_tac >>
        qmatch_asmsub_abbrev_tac `c * foo` >>
        `foo = -1w` by (unabbrev_all_tac >> blastLib.BBLAST_TAC) >>
        pop_assum SUBST_ALL_TAC >> pop_assum kall_tac >>
        qmatch_asmsub_abbrev_tac `v2w foo` >>
        `v2w foo = (11 >< 0) (-1w * c - 0x100w)` by (
          qpat_x_assum `c ≤ _` mp_tac >> qpat_x_assum `_ ≤ c` mp_tac >>
          unabbrev_all_tac >> blastLib.BBLAST_TAC) >>
        pop_assum SUBST_ALL_TAC >> pop_assum kall_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`Inst (Mem Store32 n (Addr n' c))`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        next_state_tac0 true (fn l => List.nth (l,0))
          filter_reg_31 `l3_env 0n (THE $ NextStateARM8 l3)` >>
        drule_all lem33 >> simp[] >> disch_then SUBST_ALL_TAC >>
        pop_assum mp_tac >> impl_tac >- simp[alignmentTheory.aligned_numeric] >>
        strip_tac >> gvs[] >> impl_tac
        >- (
          gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
        interference `l3_env'` >> simp[] >> conj_tac
        >- gvs[interference_ok_def, arm8_asl_proj_def] >>
        l3_state_tac[] >> gvs[] >>
        pop_assum mp_tac >> blastLib.BBLAST_TAC
        )
      >- (
        unabbrev_all_tac >> encode >> asserts >>
        imp_res_tac bytes_in_memory_thm >> gvs[] >>
        next_state_tac0 false (fn l => List.nth (l,0)) filter_reg_31 `l3` >>
        pop_assum mp_tac >> impl_tac
        >- gvs[target_state_rel_def, arm8_target_def, arm8_config_def] >>
        ntac 2 strip_tac >> gvs[] >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >>
        pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
        (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
        imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[] >> gvs[] >>
        pop_assum mp_tac >> blastLib.BBLAST_TAC
        )
      >- ( (* Mem Store n (Addr n' c) *)
        unabbrev_all_tac >> encode >>
        drule_all lem35 >> strip_tac >> gvs[] >> asserts >>
        `aligned 2 (c + l3.REG (n2w n'))` by imp_res_tac lem14b >>
        split_bytes_in_memory_tac 4 >> next_l3_tac `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`Inst (Mem Store32 n (Addr n' c))`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        next_state_tac0 false (fn l => List.nth (l,0))
          filter_reg_31 `l3_env 0n (THE $ NextStateARM8 l3)` >>
        impl_tac
        >- (
          gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
        irule_at Any $ iffLR l3_asl_target_state_rel >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
        interference `l3_env'` >> simp[] >> conj_tac
        >- gvs[interference_ok_def, arm8_asl_proj_def] >>
        l3_state_tac[] >>
        simp[mem_dword_def, ExtendWord_def] >> simp[SF wordsLib.WORD_EXTRACT_ss] >>
        gvs[] >> pop_assum mp_tac >> blastLib.BBLAST_TAC
        )
      )
    >- (Cases_on `f` >> encode) (* FP *)
    )
  >- ( (* Jump *)
    print_tac "Jump" >>
    encode >> asserts >> next_l3_tac `l3` >> strip_tac >>
    qcollapse_tac `(27 >< 2) c @@ (0w : word2)` >>
    irule_at Any $ iffLR l3_asl_target_state_rel >>
    drule_all l3_asl_interference_ok >> strip_tac >>
    pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
    (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
    imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[]
    >- (
      drule $ cj 1 alignmentTheory.aligned_add_sub >>
      disch_then $ qspec_then `sw2sw ((27 >< 2) c @@ (0w : 2 word))` assume_tac >>
      gvs[] >> simp[alignmentTheory.aligned_extract, SF WORD_EXTRACT_ss]
      )
    >- (
      qsuff_tac `c = sw2sw ((27 >< 2) c @@ (0w : word2))` >> rw[]
      >- (pop_assum (fn th => simp[Once th, SimpLHS])) >>
      irule lem9 >> simp[]
      )
    )
  >- ( (* JumpCmp *)
    Cases_on `r`
    >- ( (* Reg *)
      print_tac "JumpCmp - Reg" >>
      Cases_on `c` >> encode >> asserts
      >- ( (* Equal *)
        split_bytes_in_memory_tac 4 >>
        next_state_tac0 true List.last List.tl `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`JumpCmp Equal n (Reg n') c0`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        Cases_on `l3.REG (n2w n) = l3.REG (n2w n')` >> gvs[]
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) List.tl
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[alignmentTheory.aligned_numeric] >>
          map_every (C qpat_x_assum mp_tac) [
            `c0 ≤ _`,`_ ≤ c0`,`aligned _ c0`,`aligned _ l3.PC`] >>
          simp[alignmentTheory.aligned_extract] >>
          blastLib.BBLAST_TAC
          )
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) (fn l => [hd l])
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          pop_assum mp_tac >> impl_keep_tac
          >- (
            rewrite_tac[GSYM $ SIMP_CONV (srw_ss()) [] ``-x:word64``] >>
            rewrite_tac[GSYM word_sub_def] >>
            rewrite_tac[WORD_EQ_SUB_ZERO] >> simp[]
            ) >>
          strip_tac >> gvs[] >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[]
          )
        )
      >- ( (* Lower *)
        split_bytes_in_memory_tac 4 >>
        next_state_tac0 true List.last List.tl `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`JumpCmp Lower n (Reg n') c0`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        Cases_on `l3.REG (n2w n) <+ l3.REG (n2w n')` >> gvs[]
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) List.tl
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[alignmentTheory.aligned_numeric] >>
          map_every (C qpat_x_assum mp_tac) [
            `c0 ≤ _`,`_ ≤ c0`,`aligned _ c0`,`aligned _ l3.PC`] >>
          simp[alignmentTheory.aligned_extract] >>
          blastLib.BBLAST_TAC
          )
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) (fn l => [hd l])
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[]
          )
        )
      >- ( (* Less *)
        split_bytes_in_memory_tac 4 >>
        next_state_tac0 true List.last List.tl `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`JumpCmp Less n (Reg n') c0`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        Cases_on `l3.REG (n2w n) < l3.REG (n2w n')` >> gvs[]
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) List.tl
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          pop_assum mp_tac >> impl_keep_tac
          >- (
            rewrite_tac[GSYM $ SIMP_CONV (srw_ss()) [] ``-x:word64``] >>
            rewrite_tac[GSYM word_sub_def] >>
            simp[addressTheory.WORD_CMP_NORMALISE]
            ) >>
          strip_tac >> gvs[] >> impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[alignmentTheory.aligned_numeric] >>
          map_every (C qpat_x_assum mp_tac) [
            `c0 ≤ _`,`_ ≤ c0`,`aligned _ c0`,`aligned _ l3.PC`] >>
          simp[alignmentTheory.aligned_extract] >>
          blastLib.BBLAST_TAC
          )
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) (fn l => [hd l])
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          pop_assum mp_tac >> impl_keep_tac
          >- (
            rewrite_tac[GSYM $ SIMP_CONV (srw_ss()) [] ``-x:word64``] >>
            rewrite_tac[GSYM word_sub_def] >>
            simp[addressTheory.WORD_CMP_NORMALISE] >> gvs[WORD_NOT_LESS]
            ) >>
          strip_tac >> gvs[] >> impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[]
          )
        )
      >- ( (* Test *)
        split_bytes_in_memory_tac 4 >>
        next_state_tac0 true List.last List.tl `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`JumpCmp Test n (Reg n') c0`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        Cases_on `l3.REG (n2w n) && l3.REG (n2w n') = 0w` >> gvs[]
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) List.tl
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[alignmentTheory.aligned_numeric] >>
          map_every (C qpat_x_assum mp_tac) [
            `c0 ≤ _`,`_ ≤ c0`,`aligned _ c0`,`aligned _ l3.PC`] >>
          simp[alignmentTheory.aligned_extract] >>
          blastLib.BBLAST_TAC
          )
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) (fn l => [hd l])
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[]
          )
        )
      >- ( (* NotEqual *)
        split_bytes_in_memory_tac 4 >>
        next_state_tac0 true List.last List.tl `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`JumpCmp NotEqual n (Reg n') c0`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        Cases_on `l3.REG (n2w n) <> l3.REG (n2w n')` >> gvs[]
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) List.tl
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          pop_assum mp_tac >> impl_keep_tac
          >- (
            rewrite_tac[GSYM $ SIMP_CONV (srw_ss()) [] ``-x:word64``] >>
            rewrite_tac[GSYM word_sub_def] >>
            rewrite_tac[WORD_EQ_SUB_ZERO] >> simp[]
            ) >>
          strip_tac >> gvs[] >> impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[alignmentTheory.aligned_numeric] >>
          map_every (C qpat_x_assum mp_tac) [
            `c0 ≤ _`,`_ ≤ c0`,`aligned _ c0`,`aligned _ l3.PC`] >>
          simp[alignmentTheory.aligned_extract] >>
          blastLib.BBLAST_TAC
          )
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) (fn l => [hd l])
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[]
          )
        )
      >- ( (* NotLower *)
        split_bytes_in_memory_tac 4 >>
        next_state_tac0 true List.last List.tl `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`JumpCmp NotLower n (Reg n') c0`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        Cases_on `¬(l3.REG (n2w n) <+ l3.REG (n2w n'))` >> gvs[]
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) List.tl
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[alignmentTheory.aligned_numeric] >>
          map_every (C qpat_x_assum mp_tac) [
            `c0 ≤ _`,`_ ≤ c0`,`aligned _ c0`,`aligned _ l3.PC`] >>
          simp[alignmentTheory.aligned_extract] >>
          blastLib.BBLAST_TAC
          )
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) (fn l => [hd l])
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[]
          )
        )
      >- ( (* NotLess *)
        split_bytes_in_memory_tac 4 >>
        next_state_tac0 true List.last List.tl `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`JumpCmp NotLess n (Reg n') c0`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        Cases_on `¬(l3.REG (n2w n) < l3.REG (n2w n'))` >> gvs[]
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) List.tl
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          pop_assum mp_tac >> impl_keep_tac
          >- (
            rewrite_tac[GSYM $ SIMP_CONV (srw_ss()) [] ``-x:word64``] >>
            rewrite_tac[GSYM word_sub_def] >>
            simp[addressTheory.WORD_CMP_NORMALISE] >> gvs[WORD_NOT_LESS]
            ) >>
          strip_tac >> gvs[] >> impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[alignmentTheory.aligned_numeric] >>
          map_every (C qpat_x_assum mp_tac) [
            `c0 ≤ _`,`_ ≤ c0`,`aligned _ c0`,`aligned _ l3.PC`] >>
          simp[alignmentTheory.aligned_extract] >>
          blastLib.BBLAST_TAC
          )
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) (fn l => [hd l])
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          pop_assum mp_tac >> impl_keep_tac
          >- (
            rewrite_tac[GSYM $ SIMP_CONV (srw_ss()) [] ``-x:word64``] >>
            rewrite_tac[GSYM word_sub_def] >>
            simp[addressTheory.WORD_CMP_NORMALISE]
            ) >>
          strip_tac >> gvs[] >> impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[]
          )
        )
      >- ( (* NotTest *)
        split_bytes_in_memory_tac 4 >>
        next_state_tac0 true List.last List.tl `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`JumpCmp NotTest n (Reg n') c0`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        Cases_on `l3.REG (n2w n) && l3.REG (n2w n') ≠ 0w` >> gvs[]
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) List.tl
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[alignmentTheory.aligned_numeric] >>
          map_every (C qpat_x_assum mp_tac) [
            `c0 ≤ _`,`_ ≤ c0`,`aligned _ c0`,`aligned _ l3.PC`] >>
          simp[alignmentTheory.aligned_extract] >>
          blastLib.BBLAST_TAC
          )
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) (fn l => [hd l])
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[]
          )
        )
      )
    >- ( (* Imm *)
      print_tac "JumpCmp - Imm" >>
      Cases_on `c` >> encode >> asserts
      >- ( (* Equal - 1 *)
        split_bytes_in_memory_tac 4 >>
        next_state_tac0 true List.last List.tl `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`JumpCmp Equal n (Imm c') c0`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        Cases_on `l3.REG (n2w n) = c'` >> gvs[]
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) List.tl
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[alignmentTheory.aligned_numeric] >>
          map_every (C qpat_x_assum mp_tac) [
            `c0 ≤ _`,`_ ≤ c0`,`aligned _ c0`,`aligned _ l3.PC`] >>
          simp[alignmentTheory.aligned_extract] >>
          blastLib.BBLAST_TAC
          )
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) (fn l => [hd l])
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          pop_assum mp_tac >> impl_keep_tac
          >- (
            rewrite_tac[GSYM $ SIMP_CONV (srw_ss()) [] ``-x:word64``] >>
            rewrite_tac[Once WORD_ADD_COMM] >>
            rewrite_tac[GSYM word_sub_def] >>
            rewrite_tac[WORD_EQ_SUB_ZERO] >> simp[]
            ) >>
          strip_tac >> gvs[] >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[]
          )
        )
      >- ( (* Equal - 2 *)
        split_bytes_in_memory_tac 4 >>
        next_state_tac0 true List.last List.tl `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`JumpCmp Equal n (Imm c') c0`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        Cases_on `l3.REG (n2w n) = c'` >> gvs[]
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) List.tl
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          pop_assum mp_tac >> impl_keep_tac >- (imp_res_tac lem23 >> gvs[]) >>
          strip_tac >> gvs[] >> impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[alignmentTheory.aligned_numeric] >>
          map_every (C qpat_x_assum mp_tac) [
            `c0 ≤ _`,`_ ≤ c0`,`aligned _ c0`,`aligned _ l3.PC`] >>
          simp[alignmentTheory.aligned_extract] >>
          blastLib.BBLAST_TAC
          )
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) (fn l => [hd l])
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          pop_assum mp_tac >> impl_keep_tac
          >- (
            imp_res_tac lem23 >> gvs[] >>
            rewrite_tac[GSYM $ SIMP_CONV (srw_ss()) [] ``-x:word64``] >>
            rewrite_tac[Once WORD_ADD_COMM] >>
            rewrite_tac[GSYM word_sub_def] >>
            rewrite_tac[WORD_EQ_SUB_ZERO] >> simp[]
            ) >>
          strip_tac >> gvs[] >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[]
          )
        )
      >- ( (* Lower - 1 *)
        split_bytes_in_memory_tac 4 >>
        next_state_tac0 true List.last List.tl `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`JumpCmp Lower n (Imm c') c0`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        Cases_on `l3.REG (n2w n) <+ c'` >> gvs[]
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) List.tl
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[alignmentTheory.aligned_numeric] >>
          map_every (C qpat_x_assum mp_tac) [
            `c0 ≤ _`,`_ ≤ c0`,`aligned _ c0`,`aligned _ l3.PC`] >>
          simp[alignmentTheory.aligned_extract] >>
          blastLib.BBLAST_TAC
          )
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) (fn l => [hd l])
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[]
          )
        )
      >- ( (* Lower - 2 *)
        split_bytes_in_memory_tac 4 >>
        next_state_tac0 true List.last List.tl `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`JumpCmp Lower n (Imm c') c0`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        Cases_on `l3.REG (n2w n) <+ c'` >> gvs[]
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) List.tl
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[alignmentTheory.aligned_numeric] >>
          map_every (C qpat_x_assum mp_tac) [
            `c0 ≤ _`,`_ ≤ c0`,`aligned _ c0`,`aligned _ l3.PC`] >>
          simp[alignmentTheory.aligned_extract] >>
          blastLib.BBLAST_TAC
          )
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) (fn l => [hd l])
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[]
          )
        )
      >- ( (* Less - 1 *)
        split_bytes_in_memory_tac 4 >>
        next_state_tac0 true List.last List.tl `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`JumpCmp Less n (Imm c') c0`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        Cases_on `l3.REG (n2w n) < c'` >> gvs[]
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) List.tl
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          pop_assum mp_tac >> impl_keep_tac
          >- (
            rewrite_tac[GSYM $ SIMP_CONV (srw_ss()) [] ``-x:word64``] >>
            once_rewrite_tac[WORD_ADD_COMM] >>
            rewrite_tac[GSYM word_sub_def] >>
            simp[addressTheory.WORD_CMP_NORMALISE]
            ) >>
          strip_tac >> gvs[] >> impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[alignmentTheory.aligned_numeric] >>
          map_every (C qpat_x_assum mp_tac) [
            `c0 ≤ _`,`_ ≤ c0`,`aligned _ c0`,`aligned _ l3.PC`] >>
          simp[alignmentTheory.aligned_extract] >>
          blastLib.BBLAST_TAC
          )
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) (fn l => [hd l])
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          pop_assum mp_tac >> impl_keep_tac
          >- (
            rewrite_tac[GSYM $ SIMP_CONV (srw_ss()) [] ``-x:word64``] >>
            once_rewrite_tac[WORD_ADD_COMM] >>
            rewrite_tac[GSYM word_sub_def] >>
            simp[addressTheory.WORD_CMP_NORMALISE] >> gvs[WORD_NOT_LESS]
            ) >>
          strip_tac >> gvs[] >> impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[]
          )
        )
      >- ( (* Less - 2 *)
        split_bytes_in_memory_tac 4 >>
        next_state_tac0 true List.last List.tl `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`JumpCmp Less n (Imm c') c0`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        Cases_on `l3.REG (n2w n) < c'` >> gvs[]
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) List.tl
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          pop_assum mp_tac >> impl_keep_tac
          >- (
            imp_res_tac lem23 >> gvs[] >>
            rewrite_tac[GSYM $ SIMP_CONV (srw_ss()) [] ``-x:word64``] >>
            once_rewrite_tac[WORD_ADD_COMM] >>
            rewrite_tac[GSYM word_sub_def] >>
            simp[addressTheory.WORD_CMP_NORMALISE]
            ) >>
          strip_tac >> gvs[] >> impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[alignmentTheory.aligned_numeric] >>
          map_every (C qpat_x_assum mp_tac) [
            `c0 ≤ _`,`_ ≤ c0`,`aligned _ c0`,`aligned _ l3.PC`] >>
          simp[alignmentTheory.aligned_extract] >>
          blastLib.BBLAST_TAC
          )
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) (fn l => [hd l])
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          pop_assum mp_tac >> impl_keep_tac
          >- (
            imp_res_tac lem23 >> gvs[] >>
            rewrite_tac[GSYM $ SIMP_CONV (srw_ss()) [] ``-x:word64``] >>
            once_rewrite_tac[WORD_ADD_COMM] >>
            rewrite_tac[GSYM word_sub_def] >>
            simp[addressTheory.WORD_CMP_NORMALISE] >> gvs[WORD_NOT_LESS]
            ) >>
          strip_tac >> gvs[] >> impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[]
          )
        )
      >- ( (* Test *)
        split_bytes_in_memory_tac 4 >>
        imp_res_tac Decode_EncodeBitMask >>
        next_state_tac0 true List.last List.tl `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`JumpCmp Test n (Imm c') c0`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        Cases_on `l3.REG (n2w n) && c' = 0w` >> gvs[]
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) List.tl
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[alignmentTheory.aligned_numeric] >>
          map_every (C qpat_x_assum mp_tac) [
            `c0 ≤ _`,`_ ≤ c0`,`aligned _ c0`,`aligned _ l3.PC`] >>
          simp[alignmentTheory.aligned_extract] >>
          blastLib.BBLAST_TAC
          )
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) (fn l => [hd l])
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[]
          )
        )
      >- ( (* NotEqual - 1 *)
        split_bytes_in_memory_tac 4 >>
        next_state_tac0 true List.last List.tl `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`JumpCmp NotEqual n (Imm c') c0`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        Cases_on `l3.REG (n2w n) <> c'` >> gvs[]
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) List.tl
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          pop_assum mp_tac >> impl_keep_tac
          >- (
            rewrite_tac[GSYM $ SIMP_CONV (srw_ss()) [] ``-x:word64``] >>
            rewrite_tac[Once WORD_ADD_COMM] >>
            rewrite_tac[GSYM word_sub_def] >>
            rewrite_tac[WORD_EQ_SUB_ZERO] >> simp[]
            ) >>
          strip_tac >> gvs[] >> impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[alignmentTheory.aligned_numeric] >>
          map_every (C qpat_x_assum mp_tac) [
            `c0 ≤ _`,`_ ≤ c0`,`aligned _ c0`,`aligned _ l3.PC`] >>
          simp[alignmentTheory.aligned_extract] >>
          blastLib.BBLAST_TAC
          )
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) (fn l => [hd l])
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[]
          )
        )
      >- ( (* NotEqual - 2 *)
        split_bytes_in_memory_tac 4 >>
        next_state_tac0 true List.last List.tl `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`JumpCmp NotEqual n (Imm c') c0`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        Cases_on `l3.REG (n2w n) <> c'` >> gvs[]
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) List.tl
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          pop_assum mp_tac >> impl_keep_tac
          >- (
            imp_res_tac lem23 >> gvs[] >>
            rewrite_tac[GSYM $ SIMP_CONV (srw_ss()) [] ``-x:word64``] >>
            rewrite_tac[Once WORD_ADD_COMM] >>
            rewrite_tac[GSYM word_sub_def] >>
            rewrite_tac[WORD_EQ_SUB_ZERO] >> simp[]
            ) >>
          strip_tac >> gvs[] >> impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[alignmentTheory.aligned_numeric] >>
          map_every (C qpat_x_assum mp_tac) [
            `c0 ≤ _`,`_ ≤ c0`,`aligned _ c0`,`aligned _ l3.PC`] >>
          simp[alignmentTheory.aligned_extract] >>
          blastLib.BBLAST_TAC
          )
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) (fn l => [hd l])
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          pop_assum mp_tac >> impl_keep_tac >- (imp_res_tac lem23 >> gvs[]) >>
          strip_tac >> gvs[] >> impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[]
          )
        )
      >- ( (* NotLower - 1 *)
        split_bytes_in_memory_tac 4 >>
        next_state_tac0 true List.last List.tl `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`JumpCmp NotLower n (Imm c') c0`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        Cases_on `¬(l3.REG (n2w n) <+ c')` >> gvs[]
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) List.tl
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[alignmentTheory.aligned_numeric] >>
          map_every (C qpat_x_assum mp_tac) [
            `c0 ≤ _`,`_ ≤ c0`,`aligned _ c0`,`aligned _ l3.PC`] >>
          simp[alignmentTheory.aligned_extract] >>
          blastLib.BBLAST_TAC
          )
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) (fn l => [hd l])
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[]
          )
        )
      >- ( (* NotLower - 2 *)
        split_bytes_in_memory_tac 4 >>
        next_state_tac0 true List.last List.tl `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`JumpCmp NotLower n (Imm c') c0`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        Cases_on `¬(l3.REG (n2w n) <+ c')` >> gvs[]
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) List.tl
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[alignmentTheory.aligned_numeric] >>
          map_every (C qpat_x_assum mp_tac) [
            `c0 ≤ _`,`_ ≤ c0`,`aligned _ c0`,`aligned _ l3.PC`] >>
          simp[alignmentTheory.aligned_extract] >>
          blastLib.BBLAST_TAC
          )
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) (fn l => [hd l])
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[]
          )
        )
      >- ( (* NotLess - 1 *)
        split_bytes_in_memory_tac 4 >>
        next_state_tac0 true List.last List.tl `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`JumpCmp NotLess n (Imm c') c0`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        Cases_on `¬(l3.REG (n2w n) < c')` >> gvs[]
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) List.tl
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          pop_assum mp_tac >> impl_keep_tac
          >- (
            rewrite_tac[GSYM $ SIMP_CONV (srw_ss()) [] ``-x:word64``] >>
            once_rewrite_tac[WORD_ADD_COMM] >>
            rewrite_tac[GSYM word_sub_def] >>
            simp[addressTheory.WORD_CMP_NORMALISE] >> gvs[WORD_NOT_LESS]
            ) >>
          strip_tac >> gvs[] >> impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[alignmentTheory.aligned_numeric] >>
          map_every (C qpat_x_assum mp_tac) [
            `c0 ≤ _`,`_ ≤ c0`,`aligned _ c0`,`aligned _ l3.PC`] >>
          simp[alignmentTheory.aligned_extract] >>
          blastLib.BBLAST_TAC
          )
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) (fn l => [hd l])
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          pop_assum mp_tac >> impl_keep_tac
          >- (
            rewrite_tac[GSYM $ SIMP_CONV (srw_ss()) [] ``-x:word64``] >>
            once_rewrite_tac[GSYM WORD_ADD_COMM] >>
            rewrite_tac[GSYM word_sub_def] >>
            simp[addressTheory.WORD_CMP_NORMALISE]
            ) >>
          strip_tac >> gvs[] >> impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[]
          )
        )
      >- ( (* NotLess - 2 *)
        split_bytes_in_memory_tac 4 >>
        next_state_tac0 true List.last List.tl `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`JumpCmp NotLess n (Imm c') c0`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        Cases_on `¬(l3.REG (n2w n) < c')` >> gvs[]
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) List.tl
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          pop_assum mp_tac >> impl_keep_tac
          >- (
            imp_res_tac lem23 >> gvs[] >>
            rewrite_tac[GSYM $ SIMP_CONV (srw_ss()) [] ``-x:word64``] >>
            once_rewrite_tac[WORD_ADD_COMM] >>
            rewrite_tac[GSYM word_sub_def] >>
            simp[addressTheory.WORD_CMP_NORMALISE] >> gvs[WORD_NOT_LESS]
            ) >>
          strip_tac >> gvs[] >> impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[alignmentTheory.aligned_numeric] >>
          map_every (C qpat_x_assum mp_tac) [
            `c0 ≤ _`,`_ ≤ c0`,`aligned _ c0`,`aligned _ l3.PC`] >>
          simp[alignmentTheory.aligned_extract] >>
          blastLib.BBLAST_TAC
          )
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) (fn l => [hd l])
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          pop_assum mp_tac >> impl_keep_tac
          >- (
            imp_res_tac lem23 >> gvs[] >>
            rewrite_tac[GSYM $ SIMP_CONV (srw_ss()) [] ``-x:word64``] >>
            once_rewrite_tac[GSYM WORD_ADD_COMM] >>
            rewrite_tac[GSYM word_sub_def] >>
            simp[addressTheory.WORD_CMP_NORMALISE]
            ) >>
          strip_tac >> gvs[] >> impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[]
          )
        )
      >- ( (* NotTest *)
        split_bytes_in_memory_tac 4 >>
        imp_res_tac Decode_EncodeBitMask >>
        next_state_tac0 true List.last List.tl `l3` >> strip_tac >>
        drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
        pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
        >- (
          simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
          goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
          simp[alignmentTheory.aligned_numeric]
          ) >>
        drule l3_asl_next >>
        disch_then $ qspecl_then [`JumpCmp NotTest n (Imm c') c0`,`1`] mp_tac >>
        encode >>
        interference `l3_env` >> imp_res_tac $ Q.SPEC `4w` bytes_in_memory_thm2 >>
        `∀a. a ∈ s1.mem_domain ⇒
          (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
          gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
        Cases_on `l3.REG (n2w n) && c' ≠ 0w` >> gvs[]
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) List.tl
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[alignmentTheory.aligned_numeric] >>
          map_every (C qpat_x_assum mp_tac) [
            `c0 ≤ _`,`_ ≤ c0`,`aligned _ c0`,`aligned _ l3.PC`] >>
          simp[alignmentTheory.aligned_extract] >>
          blastLib.BBLAST_TAC
          )
        >- (
          next_state_tac0 false (fn l => List.nth (l,0)) (fn l => [hd l])
            `l3_env 0n (THE $ NextStateARM8 l3)` >>
          impl_tac
          >- (
            gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
            simp[alignmentTheory.aligned_numeric]
            ) >>
          strip_tac >> imp_res_tac l3_asl_target >> simp[] >>
          irule_at Any $ iffLR l3_asl_target_state_rel >>
          drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
          pop_assum $ qspec_then `1` assume_tac >> goal_assum drule >>
          interference `l3_env'` >> simp[] >> conj_tac
          >- gvs[interference_ok_def, arm8_asl_proj_def] >>
          l3_state_tac[]
          )
        )
      )
    )
  >- ( (* Call *)
    print_tac "Call" >>
    encode >> asserts >>
    next_l3_tac `l3` >> strip_tac >>
    imp_res_tac Decode_EncodeBitMask >> gvs[] >>
    irule_at Any $ iffLR l3_asl_target_state_rel >>
    drule_all l3_asl_interference_ok >> strip_tac >>
    pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
    (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
    qcollapse_tac `(27 >< 2) c @@ (0w :word2)` >>
    imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[]
    >- (
      drule $ cj 1 alignmentTheory.aligned_add_sub >>
      disch_then $ qspec_then `sw2sw ((27 >< 2) c @@ (0w : 2 word))` assume_tac >>
      gvs[] >> simp[alignmentTheory.aligned_extract, SF WORD_EXTRACT_ss]
      )
    >- (
      qsuff_tac `c = sw2sw ((27 >< 2) c @@ (0w : word2))` >> rw[]
      >- (pop_assum (fn th => simp[Once th, SimpLHS])) >>
      irule lem9 >> simp[]
      )
    )
  >- ( (* JumpReg *)
    print_tac "JumpReg" >>
    encode >> asserts >>
    next_l3_tac `l3` >> strip_tac >>
    imp_res_tac Decode_EncodeBitMask >> gvs[] >>
    irule_at Any $ iffLR l3_asl_target_state_rel >>
    drule_all l3_asl_interference_ok >> strip_tac >>
    pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
    (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
    imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[]
    )
  >- ( (* Loc *)
    print_tac "Loc" >>
    Cases_on `sw2sw (INT_MINw :word20) ≤ c ∧ c ≤ sw2sw (INT_MAXw :word20)`
    >- (
      encode >> asserts >>
      next_l3_tac `l3` >> strip_tac >>
      irule_at Any $ iffLR l3_asl_target_state_rel >>
      drule_all l3_asl_interference_ok >> strip_tac >>
      pop_assum $ qspec_then `0` assume_tac >> gvs[] >> goal_assum drule >>
      (conj_tac >- gvs[interference_ok_def, arm8_asl_proj_def]) >>
      qcollapse_tac `(20 >< 2) c @@ (0w :word2)` >>
      imp_res_tac l3_asl_target >> simp[] >> l3_state_tac[] >>
      qsuff_tac `c = sw2sw ((20 >< 2) c @@ (0w : word2))` >> rw[]
      >- (pop_assum (fn th => simp[Once th, SimpLHS])) >>
      irule lem10 >> simp[]
      ) >>
    NO_STRIP_REV_FULL_SIMP_TAC (srw_ss()++ARITH_ss++boolSimps.LET_ss) enc_rwts >>
    last_x_assum mp_tac >> IF_CASES_TAC >- gvs[] >> strip_tac >>
    gvs[DISJ_EQ_IMP] >>
    `n2w n ≠ 26w : word5` by gvs[lem1] >>
    encode >> asserts >>
    split_bytes_in_memory_tac 4 >>
    next_l3_tac `l3` >> strip_tac >>
    drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
    pop_assum $ qspec_then `0` assume_tac >> simp[GSYM CONJ_ASSOC] >> conj_asm1_tac
    >- (
      simp[arm8_asl_ok] >> gvs[interference_ok_def, arm8_asl_proj_def] >>
      goal_assum drule >> simp[] >> gvs[arm8_proj_def, arm8_ok_def] >>
      simp[alignmentTheory.aligned_numeric]
      ) >>

    drule l3_asl_next >>
    disch_then $ qspecl_then [`Loc n c`,`1`] mp_tac >>
    encode >> IF_CASES_TAC >> gvs[DISJ_EQ_IMP] >>
    split_bytes_in_memory_tac 4 >>
    interference `l3_env` >>
    drule_all $ Q.SPEC `4w` bytes_in_memory_thm2 >> strip_tac >> gvs[] >>
    `∀a. a ∈ s1.mem_domain ⇒
      (l3_env 0 (THE $ NextStateARM8 l3)).MEM a = (THE $ NextStateARM8 l3).MEM a` by
      gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
    next_state_tac0 false (fn l => List.nth (l,1))
      filter_reg_31 `l3_env 0n (THE $ NextStateARM8 l3)` >>
    impl_tac
    >- (
      gvs[interference_ok_def, arm8_asl_proj_def, arm8_proj_def, arm8_ok_def] >>
      simp[alignmentTheory.aligned_numeric]
      ) >>
    strip_tac >> drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
    pop_assum $ qspec_then `1` assume_tac >>

    drule l3_asl_next >>
    disch_then $ qspecl_then [`Loc n c`,`2`] mp_tac >>
    encode >> IF_CASES_TAC >> gvs[DISJ_EQ_IMP] >>
    split_bytes_in_memory_tac 4 >>
    interference `l3_env'` >>
    drule_all $ Q.SPEC `8w` bytes_in_memory_thm2 >> strip_tac >> gvs[] >>
    qmatch_goalsub_abbrev_tac `l3_env' _ l3_state` >>
    `∀a. a ∈ s1.mem_domain ⇒ (l3_env' 1 l3_state).MEM a = l3_state.MEM a` by
      gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
    unabbrev_all_tac >>
    imp_res_tac interference_ok_def >> gvs[arm8_proj_def, arm8_ok_def] >>
    simp[alignmentTheory.aligned_numeric, GSYM AND_IMP_INTRO] >>
    impl_tac >- gvs[arm8_asl_proj_def] >>
    next_state_tac0 false (fn l => List.nth (l,1)) filter_reg_31
      `l3_env' 1n $ THE $ NextStateARM8 $ l3_env 0n $ THE $ NextStateARM8 l3` >>
    strip_tac >> gvs[] >>
    drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
    pop_assum $ qspec_then `2` assume_tac >>

    drule l3_asl_next >>
    disch_then $ qspecl_then [`Loc n c`,`3`] mp_tac >>
    encode >> IF_CASES_TAC >> gvs[DISJ_EQ_IMP] >>
    split_bytes_in_memory_tac 4 >>
    interference `l3_env''` >>
    drule_all $ Q.SPEC `12w` bytes_in_memory_thm2 >> strip_tac >> gvs[] >>
    qmatch_goalsub_abbrev_tac `l3_env'' _ l3_state` >>
    `∀a. a ∈ s1.mem_domain ⇒ (l3_env'' 1 l3_state).MEM a = l3_state.MEM a` by
      gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
    unabbrev_all_tac >>
    imp_res_tac interference_ok_def >> gvs[arm8_proj_def, arm8_ok_def] >>
    simp[alignmentTheory.aligned_numeric, GSYM AND_IMP_INTRO] >>
    impl_tac >- gvs[arm8_asl_proj_def] >>
    next_state_tac0 false (fn l => List.nth (l,1)) filter_reg_31
      `l3_env'' 2n $ THE $ NextStateARM8 $
        l3_env' 1n $ THE $ NextStateARM8 $ l3_env 0n $ THE $ NextStateARM8 l3` >>
    strip_tac >> gvs[] >>
    drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
    pop_assum $ qspec_then `3` assume_tac >>

    drule l3_asl_next >>
    disch_then $ qspecl_then [`Loc n c`,`4`] mp_tac >>
    encode >> IF_CASES_TAC >> gvs[DISJ_EQ_IMP] >>
    split_bytes_in_memory_tac 4 >>
    interference `l3_env'³'` >> gvs[] >>
    drule_all $ Q.SPEC `16w` bytes_in_memory_thm2 >> strip_tac >> gvs[] >>
    qmatch_goalsub_abbrev_tac `l3_env'³' _ l3_state` >>
    `∀a. a ∈ s1.mem_domain ⇒ (l3_env'³' 1 l3_state).MEM a = l3_state.MEM a` by
      gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
    unabbrev_all_tac >>
    imp_res_tac interference_ok_def >> gvs[arm8_proj_def, arm8_ok_def] >>
    simp[alignmentTheory.aligned_numeric, GSYM AND_IMP_INTRO] >>
    impl_tac >- gvs[arm8_asl_proj_def] >>
    next_state_tac0 false (fn l => List.nth (l,1)) filter_reg_31
      `l3_env'³' 3n $ THE $ NextStateARM8 $ l3_env'' 2n $ THE $ NextStateARM8 $
        l3_env' 1n $ THE $ NextStateARM8 $ l3_env 0n $ THE $ NextStateARM8 l3` >>
    strip_tac >> gvs[] >>
    drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
    pop_assum $ qspec_then `4` assume_tac >>

    drule l3_asl_next >>
    disch_then $ qspecl_then [`Loc n c`,`5`] mp_tac >>
    encode >> IF_CASES_TAC >> gvs[DISJ_EQ_IMP] >>
    interference `l3_env'⁴'` >> gvs[] >>
    drule_all $ Q.SPEC `20w` bytes_in_memory_thm2 >> strip_tac >> gvs[] >>
    qmatch_goalsub_abbrev_tac `l3_env'⁴' _ l3_state` >>
    `∀a. a ∈ s1.mem_domain ⇒ (l3_env'⁴' 1 l3_state).MEM a = l3_state.MEM a` by
      gvs[interference_ok_def, arm8_proj_def, set_sepTheory.fun2set_eq] >>
    unabbrev_all_tac >>
    imp_res_tac interference_ok_def >> gvs[arm8_proj_def, arm8_ok_def] >>
    simp[alignmentTheory.aligned_numeric, GSYM AND_IMP_INTRO] >>
    impl_tac >- gvs[arm8_asl_proj_def] >>
    next_state_tac0 false (fn l => List.nth (l,0)) filter_reg_31
      `l3_env'⁴' 4n $ THE $ NextStateARM8 $
        l3_env'³' 3n $ THE $ NextStateARM8 $ l3_env'' 2n $ THE $ NextStateARM8 $
          l3_env' 1n $ THE $ NextStateARM8 $ l3_env 0n $ THE $ NextStateARM8 l3` >>
    strip_tac >> gvs[] >>
    drule_all l3_asl_interference_ok >> strip_tac >> gvs[] >>
    pop_assum $ qspec_then `5` assume_tac >>

    imp_res_tac l3_asl_target >> simp[] >>
    irule_at Any $ iffLR l3_asl_target_state_rel >> goal_assum drule >>
    interference `l3_env'⁵'` >> simp[] >>
    gvs[interference_ok_def, arm8_asl_proj_def] >>
    simp[arm8_asl_ok, PULL_EXISTS] >>
    rpt $ goal_assum $ drule_at Any >> simp[arm8_ok_def] >>
    l3_state_tac[alignmentTheory.aligned_extract] >>
    qpat_x_assum `(_ >< _) l3.PC = _` mp_tac >>
    blastLib.BBLAST_TAC
    )
QED

