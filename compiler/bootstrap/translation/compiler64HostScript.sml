(*
  Host selection shared by the native 64-bit compiler programs.
*)
Theory compiler64Host
Ancestors
  compiler
Libs
  preamble

Datatype:
  compiler64_host = HostX64 | HostArm8
End

Definition host_config_def:
  host_config HostX64 = x64_config ∧
  host_config HostArm8 = arm8_config
End

Definition host_args_def:
  host_args host cl =
    if host = HostArm8 ∧ find_str «--target=» cl = NONE then
      «--target=arm8» :: cl
    else cl
End

Theorem host_args_x64[simp]:
  host_args HostX64 cl = cl
Proof
  simp [host_args_def]
QED

Theorem host_args_explicit:
  find_str «--target=» cl = SOME target_name ⇒ host_args host cl = cl
Proof
  simp [host_args_def]
QED

Theorem host_args_arm8_default:
  find_str «--target=» cl = NONE ⇒
  parse_target_64 (host_args HostArm8 cl) =
    INL (arm8_backend_config,arm8_export,arm8_config)
Proof
  simp [host_args_def, compilerTheory.parse_target_64_def,
        compilerTheory.find_str_def]
  >> simp [EVAL “isPrefix «--target=» «--target=arm8»”,
           EVAL “extract «--target=arm8» 9 NONE”]
QED
