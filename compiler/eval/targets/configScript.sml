open HolKernel boolLib bossLib lcsymtacs

open arm8_targetLib arm6_targetLib mips_targetLib riscv_targetLib x64_targetLib asmLib;

val _ = new_theory"config";

val rconc = rhs o concl

(* Same config for backends *)
val source_conf = rconc(EVAL``prim_config.source_conf``)
val mod_conf = rconc(EVAL``prim_config.mod_conf``)
val clos_conf = rconc (EVAL ``clos_to_bvl$default_config``)
val bvl_conf = rconc (EVAL``bvl_to_bvi$default_config``)
val word_to_word_conf = ``<| reg_alg:=3; col_oracle := λn. NONE |>``

(* TODO: this config may need to change *)
val arm8_data_conf = ``<| tag_bits:=4; len_bits:=4; pad_bits:=3; len_size:=16|>``
val arm8_word_conf = ``<| bitmaps := []:64 word list |>``
val arm8_stack_conf = ``<|reg_names:=arm8_names;max_heap:=1000000|>``
val arm8_lab_conf = ``<|labels:=LN;asm_conf:=arm8_config;init_clock:=5|>``

val arm8_compiler_config_def = Define`
  arm8_compiler_config =
             <|source_conf:=^(source_conf);
               mod_conf:=^(mod_conf);
               clos_conf:=^(clos_conf);
               bvl_conf:=^(bvl_conf);
               data_conf:=^(arm8_data_conf);
               word_to_word_conf:=^(word_to_word_conf);
               word_conf:=^(arm8_word_conf);
               stack_conf:=^(arm8_stack_conf);
               lab_conf:=^(arm8_lab_conf)
               |>`;

val arm_data_conf = ``<| tag_bits:=0; len_bits:=0; pad_bits:=2; len_size:=8|>``
val arm_word_conf = ``<| bitmaps := []:32 word list |>``
val arm_stack_conf = ``<|reg_names:=arm_names;max_heap:=1000000|>``
val arm_lab_conf = ``<|labels:=LN;asm_conf:=arm6_config;init_clock:=5|>``

val arm_compiler_config_def = Define`
  arm_compiler_config =
             <|source_conf:=^(source_conf);
               mod_conf:=^(mod_conf);
               clos_conf:=^(clos_conf);
               bvl_conf:=^(bvl_conf);
               data_conf:=^(arm_data_conf);
               word_to_word_conf:=^(word_to_word_conf);
               word_conf:=^(arm_word_conf);
               stack_conf:=^(arm_stack_conf);
               lab_conf:=^(arm_lab_conf)
               |>`;

val mips_data_conf = ``<| tag_bits:=4; len_bits:=4; pad_bits:=3; len_size:=16|>``
val mips_word_conf = ``<| bitmaps := []:64 word list |>``
val mips_stack_conf = ``<|reg_names:=mips_names;max_heap:=1000000|>``
val mips_lab_conf = ``<|labels:=LN;asm_conf:=mips_config;init_clock:=5|>``

val mips_compiler_config_def = Define`
  mips_compiler_config =
             <|source_conf:=^(source_conf);
               mod_conf:=^(mod_conf);
               clos_conf:=^(clos_conf);
               bvl_conf:=^(bvl_conf);
               data_conf:=^(mips_data_conf);
               word_to_word_conf:=^(word_to_word_conf);
               word_conf:=^(mips_word_conf);
               stack_conf:=^(mips_stack_conf);
               lab_conf:=^(mips_lab_conf)
               |>`;

val riscv_data_conf = ``<| tag_bits:=4; len_bits:=4; pad_bits:=3; len_size:=16|>``
val riscv_word_conf = ``<| bitmaps := []:64 word list |>``
val riscv_stack_conf = ``<|reg_names:=riscv_names;max_heap:=1000000|>``
val riscv_lab_conf = ``<|labels:=LN;asm_conf:=riscv_config;init_clock:=5|>``

val riscv_compiler_config_def = Define`
  riscv_compiler_config =
             <|source_conf:=^(source_conf);
               mod_conf:=^(mod_conf);
               clos_conf:=^(clos_conf);
               bvl_conf:=^(bvl_conf);
               data_conf:=^(riscv_data_conf);
               word_to_word_conf:=^(word_to_word_conf);
               word_conf:=^(riscv_word_conf);
               stack_conf:=^(riscv_stack_conf);
               lab_conf:=^(riscv_lab_conf)
               |>`;

val x64_data_conf = ``<| tag_bits:=4; len_bits:=4; pad_bits:=3; len_size:=16|>``
val x64_word_conf = ``<| bitmaps := []:64 word list |>``
val x64_stack_conf = ``<|reg_names:=x64_names;max_heap:=1000000|>``
val x64_lab_conf = ``<|labels:=LN;asm_conf:=x64_config;init_clock:=5|>``

val x64_compiler_config_def = Define`
  x64_compiler_config =
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

val _ = export_theory();
