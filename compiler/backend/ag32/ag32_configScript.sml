(*
  Define the compiler configuration for ag32
*)
open preamble backendTheory ag32_targetTheory ag32_targetLib

val _ = new_theory"ag32_config";

val ag32_names_def = Define `
  ag32_names = LN:num num_map`

val ag32_names_def = save_thm("ag32_names_def[compute]",
  CONV_RULE (RAND_CONV EVAL) ag32_names_def);

val source_conf = rconc(EVAL``prim_config.source_conf``)
val clos_conf = rconc (EVAL ``clos_to_bvl$default_config``)
val bvl_conf = rconc (EVAL``bvl_to_bvi$default_config``)
val word_to_word_conf = ``<| reg_alg:=2; col_oracle := λn. NONE |>``
val ag32_data_conf = ``<| tag_bits:=0; len_bits:=0; pad_bits:=1; len_size:=20; has_div:=F; has_longdiv:=F; has_fp_ops:=T; has_fp_tern:=F; call_empty_ffi:=F; gc_kind:=Simple|>``
val ag32_word_conf = ``<| bitmaps := []:32 word list |>``
val ag32_stack_conf = ``<|jump:=T;reg_names:=ag32_names|>``
val ag32_lab_conf = ``<|pos:=0;ffi_names:=NONE;labels:=LN;asm_conf:=ag32_config;init_clock:=5;hash_size:=104729n|>``

val ag32_backend_config_def = Define`
  ag32_backend_config =
             <|source_conf:=^(source_conf);
               clos_conf:=^(clos_conf);
               bvl_conf:=^(bvl_conf);
               data_conf:=^(ag32_data_conf);
               word_to_word_conf:=^(word_to_word_conf);
               word_conf:=^(ag32_word_conf);
               stack_conf:=^(ag32_stack_conf);
               lab_conf:=^(ag32_lab_conf);
               tap_conf:=default_tap_config
               |>`;

val _ = export_theory();
