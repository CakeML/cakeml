open HolKernel boolLib bossLib lcsymtacs

open mips_targetLib asmLib;

val _ = new_theory"mips_config";

val rconc = rhs o concl

val source_conf = rconc(EVAL``prim_config.source_conf``)
val mod_conf = rconc(EVAL``prim_config.mod_conf``)
val clos_conf = rconc (EVAL ``clos_to_bvl$default_config``)
val bvl_conf = rconc (EVAL``bvl_to_bvi$default_config``)
(* TODO: may need to change *)
val data_conf = ``<| tag_bits:=4; len_bits:=4; pad_bits:=0; len_size:=16|>``
val word_to_word_conf = ``<| reg_alg:=3; col_oracle := λn. NONE |>``
val word_conf = ``<| bitmaps := []:64 word list |>``
val stack_conf = ``<|reg_names:=mips_names;max_heap:=1000000|>``
val lab_conf = ``<|labels:=LN;asm_conf:=mips_config;init_clock:=5|>``

val mips_compiler_config_def = Define`
  mips_compiler_config =
             <|source_conf:=^(source_conf);
               mod_conf:=^(mod_conf);
               clos_conf:=^(clos_conf);
               bvl_conf:=^(bvl_conf);
               data_conf:=^(data_conf);
               word_to_word_conf:=^(word_to_word_conf);
               word_conf:=^(word_conf);
               stack_conf:=^(stack_conf);
               lab_conf:=^(lab_conf)
               |>`;

val tes = EVAL
  ``let c = mips_compiler_config in
      names_ok c.stack_conf.reg_names
         c.lab_conf.asm_conf.reg_count
         c.lab_conf.asm_conf.avoid_regs``

val must_be_callee_saved = EVAL
  ``let c = mips_compiler_config in
    let n = (c.lab_conf.asm_conf.reg_count -
               (LENGTH c.lab_conf.asm_conf.avoid_regs + 3)) in
    let xs = [n;n+1;n+2n] in
      MAP (find_name c.stack_conf.reg_names) xs``

val _ = export_theory();
