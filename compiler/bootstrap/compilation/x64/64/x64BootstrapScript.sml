(*
  Evaluate the 64-bit version of the compiler into x64 machine code.
*)
open preamble compiler64ProgTheory eval_cake_compile_x64Lib;

val _ = new_theory "x64Bootstrap"

Definition init_conf_def:
  init_conf =
    x64_config$x64_backend_config with
    <| source_conf := prim_src_config;
       clos_conf   := clos_to_bvl$default_config
                        with known_conf := SOME
                         <| inline_max_body_size := 8; inline_factor := 0;
                            initial_inline_factor := 0; val_approx_spt := LN |>;
       bvl_conf    := bvl_to_bvi$default_config with
                        <| inline_size_limit := 3; exp_cut := 200 |>;
       word_to_word_conf :=
        (x64_config$x64_backend_config.word_to_word_conf with
           reg_alg := 4) |>
End

val init_conf_eq =
  init_conf_def |> SRULE [x64_configTheory.x64_backend_config_def,
                          backendTheory.prim_src_config_eq];

Theorem compiler64_compiled =
  eval_cake_compile_x64_general
    { prefix               = ""
    , conf_def             = init_conf_eq
    , prog_def             = compiler64_prog_def
    , run_as_explorer      = false
    , output_filename      = "cake.S"
    , output_conf_filename = SOME "config_enc_str.txt" };

val _ = export_theory ();
