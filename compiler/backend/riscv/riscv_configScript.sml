(*
  Define the compiler configuration for RISC-V
*)
open preamble backendTheory riscv_targetTheory riscv_targetLib

val _ = new_theory"riscv_config";

val riscv_names_def = Define `
  riscv_names =
  (* arguments: 10-17
       including return values: 10-11
     temporaries: 5-7, 28-31
     return address: 1
     saved regs: 8-9, 18-27
     3 = global pointer, 4 = thread pointer (not sure if they need to be avoided)
     0 avoided (hardwired zero)
     2 avoided (stack pointer)
     3 avoided (global pointer)
     31 avoided (used by encoder)
     4 avoid regs means 28 regs available for CakeML
     constraints:
       the last 3 of these (25, 26, 27) must be mapped to callee saved regs
       0 must be mapped to link reg (1)
       1-4 must be mapped to 1st-4st args (10-13)
  *)
  (insert 0 1 o
   insert 1 10 o
   insert 2 11 o
   insert 3 12 o
   insert 4 13 o
   (* the rest to make the mapping well-formed *)
   insert 10 29 o
   insert 11 30 o
   insert 12 4 o
   insert 13 28 o
   insert 28 0 o
   insert 29 2 o
   insert 30 3) LN:num num_map`;

val riscv_names_def = save_thm("riscv_names_def[compute]",
  CONV_RULE (RAND_CONV EVAL) riscv_names_def);

val source_conf = rconc(EVAL``prim_config.source_conf``)
val clos_conf = rconc (EVAL ``clos_to_bvl$default_config``)
val bvl_conf = rconc (EVAL``bvl_to_bvi$default_config``)
val word_to_word_conf = ``<| reg_alg:=3; col_oracle := λn. NONE |>``
val riscv_data_conf = ``<| tag_bits:=4; len_bits:=4; pad_bits:=2; len_size:=32; has_div:=T; has_longdiv:=F; has_fp_ops:=F; has_fp_tern:=F; call_empty_ffi:=F; gc_kind:=Simple|>``
val riscv_word_conf = ``<| bitmaps := []:64 word list |>``
val riscv_stack_conf = ``<|jump:=F;reg_names:=riscv_names|>``
val riscv_lab_conf = ``<|pos:=0;ffi_names:=NONE;labels:=LN;asm_conf:=riscv_config;init_clock:=5;hash_size:=104729n|>``

val riscv_backend_config_def = Define`
  riscv_backend_config =
             <|source_conf:=^(source_conf);
               clos_conf:=^(clos_conf);
               bvl_conf:=^(bvl_conf);
               data_conf:=^(riscv_data_conf);
               word_to_word_conf:=^(word_to_word_conf);
               word_conf:=^(riscv_word_conf);
               stack_conf:=^(riscv_stack_conf);
               lab_conf:=^(riscv_lab_conf);
               tap_conf:=default_tap_config
               |>`;

val _ = export_theory();
