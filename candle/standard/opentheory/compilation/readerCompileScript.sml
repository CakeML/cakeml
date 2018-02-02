open preamble compilationLib readerProgTheory
open x64_configTheory

val _ = new_theory "readerCompile"

val source_conf = rconc(EVAL``prim_config.source_conf``)
val mod_conf = rconc(EVAL``prim_config.mod_conf``)
val clos_conf = rconc (EVAL ``clos_to_bvl$default_config``)
val bvl_conf = rconc (EVAL``bvl_to_bvi$default_config with <| exp_cut := 200 |>``)
val word_to_word_conf = ``<| reg_alg:=3; col_oracle := λn. NONE |>``

val x64_data_conf = ``<| tag_bits:=4; len_bits:=4; pad_bits:=2; len_size:=32; has_div:=F; has_longdiv:=T; has_fp_ops:=F; call_empty_ffi:=F; gc_kind:=Simple|>``
val x64_word_conf = ``<| bitmaps := []:64 word list |>``
val x64_stack_conf = ``<|jump:=T;reg_names:=x64_names|>``
val x64_lab_conf = ``<|pos:=0;ffi_names:=NONE;labels:=LN;asm_conf:=x64_config;init_clock:=5|>``

val fast_config_def = Define`
  fast_config =
             <|source_conf:=^(source_conf);
               mod_conf:=^(mod_conf);
               clos_conf:=^(clos_conf);
               bvl_conf:=^(bvl_conf);
               data_conf:=^(x64_data_conf);
               word_to_word_conf:=^(word_to_word_conf);
               word_conf:=^(x64_word_conf);
               stack_conf:=^(x64_stack_conf);
               lab_conf:=^(x64_lab_conf)
               |>`;

val compile_fast = compile fast_config_def cbv_to_bytes_x64

val reader_compiled = save_thm("reader_compiled",
  compile_fast 1000 1000 "reader" reader_prog_def);

val _ = export_theory ();

