(*
  The compiler configurations of the CakePB executables satisfy the
  assumptions of the compiler correctness theorem: each is the default
  configuration with only clos_conf.max_app changed
*)
Theory npbc_compile_configProof
Ancestors
  backendProof x64_configProof arm8_configProof npbc_compile_config
Libs
  preamble

Theorem x64_backend_config_ok_pb:
  backend_config_ok x64_config x64_config_pb
Proof
  assume_tac x64_backend_config_ok>>
  gvs[backend_config_ok_def,x64_config_pb_def]
QED

Theorem x64_init_ok_pb:
  is_x64_machine_config mc ⇒
  mc_init_ok x64_config x64_config_pb mc
Proof
  strip_tac>>
  drule x64_init_ok>>
  simp[x64_config_pb_def]
QED

Theorem x64_config_pb_stack_conf:
  x64_config_pb.stack_conf = x64_backend_config.stack_conf
Proof
  simp[x64_config_pb_def]
QED

Theorem arm8_backend_config_ok_pb:
  backend_config_ok arm8_config arm8_config_pb
Proof
  assume_tac arm8_backend_config_ok>>
  gvs[backend_config_ok_def,arm8_config_pb_def]
QED

Theorem arm8_config_pb_stack_conf:
  arm8_config_pb.stack_conf = arm8_backend_config.stack_conf
Proof
  simp[arm8_config_pb_def]
QED
