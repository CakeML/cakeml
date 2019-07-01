(*
  Define the compiler configuration for MIPS
*)
open preamble backendTheory mips_targetTheory mips_targetLib

val _ = new_theory"mips_config";

val mips_names_def = Define `
  mips_names =
    (* source can use 24 regs (r2-r24,r31),
       target's r0 must be avoided (hardcoded to 0),
       target's r1 must be avoided (used by encoder in asm),
       target's r25 and r28 are used to set up PIC
       target's r29 must be avoided (stack pointer),
       target's r26-r27 avoided (reserved for OS kernel),
       target's r30 must be avoided (used by encoder in asm),
       source 0 must represent r31 (link register),
       source 1-4 must be r4-r7 (1st 4 args),
       top 3 (21-23) must be callee-saved (in 16-23, 28, 30) *)
    (insert 0 31 o
     insert 1 4 o
     insert 2 5 o
     insert 3 6 o
     insert 4 7 o
     (* the rest just ensures that the mapping is well-formed *)
     insert 7 2 o
     insert 5 24 o
     insert 6 3 o
     insert 24 0 o
     insert 31 1) LN:num num_map`

val mips_names_def = save_thm("mips_names_def[compute]",
  CONV_RULE (RAND_CONV EVAL) mips_names_def);

val source_conf = rconc(EVAL``prim_config.source_conf``)
val clos_conf = rconc (EVAL ``clos_to_bvl$default_config``)
val bvl_conf = rconc (EVAL``bvl_to_bvi$default_config``)
val word_to_word_conf = ``<| reg_alg:=2; col_oracle := λn. NONE |>``
val mips_data_conf = ``<| tag_bits:=4; len_bits:=4; pad_bits:=2; len_size:=32; has_div:=T; has_longdiv:=F; has_fp_ops:=T; has_fp_tern := F; call_empty_ffi:=F; gc_kind:=Simple|>``
val mips_word_conf = ``<| bitmaps := []:64 word list |>``
val mips_stack_conf = ``<|jump:=F;reg_names:=mips_names|>``
val mips_lab_conf = ``<|pos:=0;ffi_names:=NONE;labels:=LN;asm_conf:=mips_config;init_clock:=5;hash_size:=104729n|>``

val mips_backend_config_def = Define`
  mips_backend_config =
             <|source_conf:=^(source_conf);
               clos_conf:=^(clos_conf);
               bvl_conf:=^(bvl_conf);
               data_conf:=^(mips_data_conf);
               word_to_word_conf:=^(word_to_word_conf);
               word_conf:=^(mips_word_conf);
               stack_conf:=^(mips_stack_conf);
               lab_conf:=^(mips_lab_conf);
               tap_conf:=default_tap_config
               |>`;

val _ = export_theory();
