(*
  Define the target compiler configuration for ASL-derived ARMv8.
*)
open HolKernel Parse boolLib bossLib;
open asmLib arm8_targetTheory l3_equivalenceTheory;

val _ = new_theory "arm8_asl_target";

val _ = wordsLib.guess_lengths();

(********** Next-state function **********)

Definition arm8_asl_next_def:
  arm8_asl_next = do
    (* fetch *)
      write_regS BranchTaken_ref F;
      pc <- PC_read();
      instr :word32 <- Mem_read0 pc 4 AccType_IFETCH;

    (* execute *)
      write_regS SEE_ref (-1);
      ExecuteA64 instr;

    (* update PC *)
      branch_taken <- read_regS BranchTaken_ref;
      if branch_taken then returnS () else PC_set (pc + 4w)
  od
End


(********** Valid states **********)

Definition arm8_asl_mem_ok_def:
  arm8_asl_mem_ok asl ⇔
    (∀w:word64. FLOOKUP asl.tagstate (w2n w) = SOME B0) ∧
    (∀w:word64. ∃byt. LENGTH byt = 8 ∧
      FLOOKUP asl.memstate (w2n w) = SOME (MAP bitU_of_bool byt))
End

Definition arm8_asl_regs_ok_def:
  arm8_asl_regs_ok asl ⇔
    LENGTH (R_ref.read_from asl.regstate) = 32
End

Definition arm8_asl_ok_def:
  arm8_asl_ok asl ⇔
    asl_sys_regs_ok asl ∧
    (PSTATE_ref.read_from asl.regstate).ProcState_EL = 0w ∧ (* EL0 *)
    ¬word_bit 4 (SCTLR_EL1_ref.read_from asl.regstate) ∧ (* ¬SCTLR_EL1.SA0 *)
    ¬word_bit 24 (SCTLR_EL1_ref.read_from asl.regstate) ∧ (* ¬SCTLR_EL1.EOE *)
    ¬word_bit 37 (TCR_EL1_ref.read_from asl.regstate) ∧ (* ¬TCR_EL1.TBI0 *)
    ¬word_bit 38 (TCR_EL1_ref.read_from asl.regstate) ∧ (* ¬TCR_EL1.TBI1 *)
    aligned 2 (PC_ref.read_from asl.regstate) ∧ (* aligned 2 PC *)
    arm8_asl_mem_ok asl ∧ arm8_asl_regs_ok asl
End

(********** Target record **********)

Definition arm8_asl_proj_def:
  arm8_asl_proj (mem : word64 set) asl = (
    PSTATE_ref.read_from asl.regstate,
    SCTLR_EL1_ref.read_from asl.regstate,
    TCR_EL1_ref.read_from asl.regstate,
    R_ref.read_from asl.regstate,
    fun2set ($' asl.memstate o w2n, mem),
    PC_ref.read_from asl.regstate,
    asl_sys_regs_ok asl,
    arm8_asl_mem_ok asl,
    arm8_asl_regs_ok asl
    )
End

Definition arm8_asl_target_def:
  arm8_asl_target =
    <| next := SND o arm8_asl_next
     ; config := arm8_config
     ; get_pc := (λasl. PC_ref.read_from asl.regstate)
     ; get_reg := (λasl n. EL n $ R_ref.read_from asl.regstate)
     ; get_byte :=
          (λasl a:word64.  (v2w : bool list -> word8)
            (MAP (THE o bool_of_bitU) $ asl.memstate ' (w2n a)))
     ; state_ok := arm8_asl_ok
     ; proj := arm8_asl_proj
     |>
End

val _ = export_theory();

