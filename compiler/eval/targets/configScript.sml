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

val arm8_names_def = Define `
  arm8_names =
    (* source can use 30 regs (0-29),
       target's r26 must be avoided (extra encoding register),
       target's r31 must be avoided (stack pointer),
       source 0 must represent r30 (link register),
       source 1-2 must be r0,r1 (1st 2 args),
       top three (28-30) must be callee-saved (in r19-r29) *)
    (insert 0 30 o
     insert 1 0 o
     insert 2 1 o
     insert 26 2 o
     (* Next one is for well-formedness only *)
     insert 30 26) LN:num num_map`

val arm8_names_def = save_thm("arm8_names_def",
  CONV_RULE (RAND_CONV EVAL) arm8_names_def);

(* TODO: this config may need to change *)
val arm8_data_conf = ``<| tag_bits:=4; len_bits:=4; pad_bits:=2; len_size:=32; has_div:=T; has_longdiv:=F|>``
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

val arm_names_def = Define `
  arm_names =
    (* source can use 14 regs,
       target's r15 must be avoided (pc),
       target's r13 must be avoided (stack pointer),
       source 0 must represent r14 (link register),
       source 1-2 must be r0 and r1 (1st 2 arguments)
       the top three (source 11-13) must be callee-saved
       (callee-saved include: r4-r8, r10-11) *)
    (insert 0 14 o
     insert 1 0 o
     insert 2 1 o
     insert 12 8 o
     insert 13 10 o
     (* the rest just ensures that the mapping is well-formed *)
     insert 8 2 o
     insert 10 12 o
     insert 14 13) LN:num num_map`

val arm_names_def = save_thm("arm_names_def",
  CONV_RULE (RAND_CONV EVAL) arm_names_def);

val arm_data_conf = ``<| tag_bits:=0; len_bits:=0; pad_bits:=1; len_size:=20; has_div:=F; has_longdiv:=F|>``
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

val mips_names_def = Define `
  mips_names =
    (* source can use 25 regs (r2-r24,r30-r31),
       target's r0 must be avoided (hardcoded to 0),
       target's r1 must be avoided (used by encoder in asm),
       target's r25 and r28 are used to set up PIC
       target's r29 must be avoided (stack pointer),
       target's r26-r27 avoided (reserved for OS kernel),
       source 0 must represent r31 (link register),
       source 1 2 must be r4, r5 (1st 2 args),
       top 3 (22-24) must be callee-saved (in 16-23, 28, 30) *)
    (insert 0 31 o
     insert 1 4 o
     insert 2 5 o
     insert 22 21 o
     insert 23 22 o
     insert 24 23 o
     (* the rest just ensures that the mapping is well-formed *)
     insert 4 2 o
     insert 21 24 o
     insert 5 30 o
     insert 31 0 o
     insert 30 1) LN:num num_map`

val mips_names_def = save_thm("mips_names_def",
  CONV_RULE (RAND_CONV EVAL) mips_names_def);

val mips_data_conf = ``<| tag_bits:=4; len_bits:=4; pad_bits:=2; len_size:=32; has_div:=T; has_longdiv:=F|>``
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
       0 1 and 2 must be mapped to link reg (1), 1st arg (10), 2nd arg (11)
  *)
  (insert 0 1 o
   insert 1 10 o
   insert 2 11 o
   insert 3 28 o
   (* the rest to make the mapping well-formed *)
   insert 10 29 o
   insert 11 30 o
   insert 28 0 o
   insert 29 2 o
   insert 30 3) LN:num num_map`;

val riscv_names_def = save_thm("riscv_names_def",
  CONV_RULE (RAND_CONV EVAL) riscv_names_def);

val riscv_data_conf = ``<| tag_bits:=4; len_bits:=4; pad_bits:=2; len_size:=32; has_div:=T; has_longdiv:=F|>``
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

val x64_names_def = Define `
  x64_names =
    (* 16 regs, must avoid 4 and 5, names:
         r0=rax, r1=rbx, r2=rcx, r3=rdx, r4=rbp, r5=rsp, r6=rsi,
         r7=rdi, r8=r8, r9, r10, r11, r12, r13, r14, r15
       The first six arguments are passed in registers. The first
       argument (1) is passed in rdi(r7), the second(2) in rsi(r6),
       the third(3) in rdx(r3), the fourth(4) in rcx(2), the fifth(5)
       in r8 and the sixth in r9.
       Callee-saved regs: r12-r15, rbx
     *)
    (insert 1 7 o  (* arg 1 *)
     insert 2 6 o  (* arg 2 *)
  (* insert 3 3 o *)
     insert 4 2 o
     insert 5 8 o
     insert 6 9 o
     insert 11 12 o
     insert 12 13 o
     insert 13 14 o
     (* the rest just ensures that the mapping is well-formed *)
     insert 7 1 o
     insert 8 15 o
     insert 9 11 o
     insert 14 4 o
     insert 15 5) LN:num num_map`

val x64_names_def = save_thm("x64_names_def",
  CONV_RULE (RAND_CONV EVAL) x64_names_def);

val x64_data_conf = ``<| tag_bits:=4; len_bits:=4; pad_bits:=2; len_size:=32; has_div:=F; has_longdiv:=T|>``
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
