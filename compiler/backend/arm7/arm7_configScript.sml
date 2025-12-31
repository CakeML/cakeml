(*
  Define the compiler configuration for ARMv7
*)
Theory arm7_config
Ancestors
  backend arm7_target
Libs
  preamble arm7_targetLib

Definition arm7_names_def:
  arm7_names =
    (* source can use 14 regs,
       target's r15 must be avoided (pc),
       target's r13 must be avoided (stack pointer),
       source 0 must represent r14 (link register),
       source 1-4 must be r0-r3 (1st 4 arguments)
       the top three (source 11-13) must be callee-saved
       (callee-saved include: r4-r8, r10-11) *)
    (insert 0 14 o
     insert 1 0 o
     insert 2 1 o
     insert 3 2 o
     insert 4 3 o
     insert 12 8 o
     insert 13 10 o
     (* the rest just ensures that the mapping is well-formed *)
     insert 8 4 o
     insert 10 12 o
     insert 14 13) LN:num num_map
End

Theorem arm7_names_def[allow_rebind] =
  CONV_RULE (RAND_CONV EVAL) arm7_names_def

val clos_conf = rconc (EVAL ``clos_to_bvl$default_config``)
val bvl_conf = rconc (EVAL``bvl_to_bvi$default_config``)
val word_to_word_conf = ``<| reg_alg:=2; col_oracle := [] |>``
val arm7_data_conf = ``<| tag_bits:=0; len_bits:=0; pad_bits:=1; len_size:=20; has_div:=F; has_longdiv:=F; has_fp_ops:=T; has_fp_tern:=T; be:=F; call_empty_ffi:=F; gc_kind:=Simple|>``
val arm7_word_conf = ``<| bitmaps_length := 0; stack_frame_size := LN |>``
val arm7_stack_conf = ``<|jump:=T;reg_names:=arm7_names|>``
val arm7_lab_conf = ``<|inc_pos:=0;inc_ffi_names:=NONE;inc_labels:=LN;inc_sec_pos_len:=[];inc_init_clock:=5;inc_hash_size:=104729n;inc_shmem_extra:=[]|>``

Definition arm7_backend_config_def:
  arm7_backend_config =
             <|source_conf:=prim_src_config;
               clos_conf:=^(clos_conf);
               bvl_conf:=^(bvl_conf);
               data_conf:=^(arm7_data_conf);
               word_to_word_conf:=^(word_to_word_conf);
               word_conf:=^(arm7_word_conf);
               stack_conf:=^(arm7_stack_conf);
               lab_conf:=^(arm7_lab_conf);
               symbols:=[];
               tap_conf:=default_tap_config;
               exported:=[]
               |>
End

