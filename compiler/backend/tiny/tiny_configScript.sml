open preamble backendTheory tiny_targetTheory tiny_targetLib

val _ = new_theory"tiny_config";

val tiny_names_def = Define `
  tiny_names = LN:num num_map`

val tiny_names_def = save_thm("tiny_names_def",
  CONV_RULE (RAND_CONV EVAL) tiny_names_def);

val source_conf = rconc(EVAL``prim_config.source_conf``)
val mod_conf = rconc(EVAL``prim_config.mod_conf``)
val clos_conf = rconc (EVAL ``clos_to_bvl$default_config``)
val bvl_conf = rconc (EVAL``bvl_to_bvi$default_config``)
val word_to_word_conf = ``<| reg_alg:=3; col_oracle := λn. NONE |>``
val tiny_data_conf = ``<| tag_bits:=0; len_bits:=0; pad_bits:=1; len_size:=20; has_div:=F; has_longdiv:=F; has_fp_ops:=T; call_empty_ffi:=F; gc_kind:=Simple|>``
val tiny_word_conf = ``<| bitmaps := []:32 word list |>``
val tiny_stack_conf = ``<|jump:=T;reg_names:=tiny_names|>``
val tiny_lab_conf = ``<|pos:=0;ffi_names:=NONE;labels:=LN;asm_conf:=tiny_config;init_clock:=5|>``

val tiny_backend_config_def = Define`
  tiny_backend_config =
             <|source_conf:=^(source_conf);
               mod_conf:=^(mod_conf);
               clos_conf:=^(clos_conf);
               bvl_conf:=^(bvl_conf);
               data_conf:=^(tiny_data_conf);
               word_to_word_conf:=^(word_to_word_conf);
               word_conf:=^(tiny_word_conf);
               stack_conf:=^(tiny_stack_conf);
               lab_conf:=^(tiny_lab_conf)
               |>`;

val _ = export_theory();
