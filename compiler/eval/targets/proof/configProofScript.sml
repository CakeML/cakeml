open preamble
open configTheory
open backendProofTheory
open configTheory

open x64_targetProofTheory arm6_targetProofTheory arm8_targetProofTheory riscv_targetProofTheory mips_targetProofTheory

val _ = new_theory"configProof";

val x64_machine_config_def = Define`
  x64_machine_config = <|target:= x64_target; len_reg:=6 ; ptr_reg := 7 ; caller_saved_regs := [12;13;14]|>`

val x64_conf_ok = prove(``
  conf_ok x64_compiler_config x64_machine_config``,
  simp[conf_ok_def]>>rw[]>>TRY(EVAL_TAC>>NO_TAC)
  >-
    fs[x64_machine_config_def,x64_backend_correct]
  >-
    cheat (* There's probably a better way to check this than brute force?*)
  >>
  fs[markerTheory.Abbrev_def]>>EVAL_TAC>>fs[]);

val arm6_machine_config_def = Define`
  arm6_machine_config = <|target:= arm6_target ; len_reg:=1  ; ptr_reg := 0 ; caller_saved_regs := [11;12;13]|>`

val arm6_conf_ok = prove(``
  conf_ok arm_compiler_config arm6_machine_config``,
  simp[conf_ok_def]>>rw[]>>TRY(EVAL_TAC>>NO_TAC)
  >-
    fs[arm6_machine_config_def,arm6_backend_correct]
  >-
    cheat (* There's probably a better way to check this than brute force?*)
  >>
  fs[markerTheory.Abbrev_def]>>EVAL_TAC>>fs[]);

val arm8_machine_config_def = Define`
  arm8_machine_config = <|target:= arm8_target ; len_reg:=1  ; ptr_reg := 0 ; caller_saved_regs := [2;28;29]|>`

val arm8_conf_ok = prove(``
  conf_ok arm8_compiler_config arm8_machine_config``,
  simp[conf_ok_def]>>rw[]>>TRY(EVAL_TAC>>NO_TAC)
  >-
    fs[arm8_machine_config_def,arm8_backend_correct]
  >-
    cheat (* There's probably a better way to check this than brute force?*)
  >>
  fs[markerTheory.Abbrev_def]>>
  EVAL_TAC>>
  fs[]);

val riscv_machine_config_def = Define`
  riscv_machine_config = <|target:= riscv_target; len_reg:=5  ; ptr_reg := 4 ; caller_saved_regs := [27;28;29]|>`

val riscv_conf_ok = prove(``
  conf_ok riscv_compiler_config riscv_machine_config``,
  simp[conf_ok_def]>>rw[]>> TRY(EVAL_TAC>>NO_TAC)
  >-
    fs[riscv_machine_config_def,riscv_backend_correct]
  >-
    cheat (* There's probably a better way to check this than brute force?*)
  >>
  fs[markerTheory.Abbrev_def]>>
  EVAL_TAC>>
  fs[]);

val mips_machine_config_def = Define`
  mips_machine_config = <|target:= mips_target; len_reg:=5  ; ptr_reg := 4 ; caller_saved_regs := [27;28;29]|>`

val mips_conf_ok = prove(``
  conf_ok mips_compiler_config mips_machine_config``,
  simp[conf_ok_def]>>rw[]>> TRY(EVAL_TAC>>NO_TAC)
  >-
    fs[mips_machine_config_def,mips_backend_correct]
  >-
    cheat (* There's probably a better way to check this than brute force?*)
  >>
  fs[markerTheory.Abbrev_def]>>
  EVAL_TAC>>
  fs[]);

val _ = export_theory();
