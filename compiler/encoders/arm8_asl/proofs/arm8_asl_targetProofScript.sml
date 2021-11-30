(*
  Prove `encoder_correct` for ASL-derived ARMv8
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open listTheory wordsTheory finite_mapTheory wordsLib;
open asmLib asmPropsTheory arm8_asl_targetTheory
     l3_equivalenceTheory l3_equivalenceProofTheory l3_equivalenceLib
     arm8Theory arm8_targetTheory arm8_targetProofTheory;

val _ = new_theory "arm8_asl_targetProof"

val _ = wordsLib.guess_lengths();

val _ = set_grammar_ancestry [
          "arm8",
          "armv86a_termination",
          "l3_equivalence",
          "arm8_target",
          "arm8_asl_target"
          ];


(********** Lemmas **********)

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

Triviality arm8_encode_NOT_NIL[simp]:
  ∀i. arm8_encode i ≠ []
Proof
  rw[arm8_encode_def] >> CASE_TAC >> simp[]
QED

Triviality arm8_ast_NOT_NIL[simp]:
  ∀i. arm8_ast i ≠ []
Proof
  reverse Cases >> simp[arm8_ast_def, AllCaseEqs()]
  >- (
    Cases_on `r` >> simp[arm8_ast_def, AllCaseEqs(), arm8_encode_fail_def]
    ) >>
  Cases_on `i'` >> simp[arm8_ast_def, AllCaseEqs(), arm8_encode_fail_def]
  >- (
    Cases_on `a` >> simp[arm8_ast_def, AllCaseEqs(), arm8_encode_fail_def] >>
    Cases_on `r` >> simp[arm8_ast_def, AllCaseEqs(), arm8_encode_fail_def]
    )
  >- (
    Cases_on `a` >> simp[arm8_ast_def, AllCaseEqs(), arm8_encode_fail_def] >>
    Cases_on `m` >> simp[arm8_ast_def, AllCaseEqs(), arm8_encode_fail_def] >>
    simp[arm8_load_store_ast_def, AllCaseEqs()] >> pairarg_tac >> gvs[]
    )
QED

Triviality arm8_enc_NOT_NIL[simp]:
  ∀i. arm8_enc i ≠ []
Proof
  CCONTR_TAC >> gvs[arm8_enc_def] >>
  Cases_on `arm8_ast i` >> gvs[]
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


Theorem arm8_asl_encoder_correct:
  encoder_correct arm8_asl_target
Proof
  cheat (* TODO *)
QED

val _ = export_theory();
