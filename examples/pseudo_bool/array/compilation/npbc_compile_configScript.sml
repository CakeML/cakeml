(*
  The compiler configurations of the CakePB executables: the default x64
  and arm8 configurations with clos_conf.max_app raised to 20
*)
Theory npbc_compile_config
Ancestors
  x64_config arm8_config
Libs
  preamble

Definition x64_config_pb_def:
  x64_config_pb =
    x64_backend_config with
      clos_conf := (x64_backend_config.clos_conf with max_app := 20)
End

Definition arm8_config_pb_def:
  arm8_config_pb =
    arm8_backend_config with
      clos_conf := (arm8_backend_config.clos_conf with max_app := 20)
End
