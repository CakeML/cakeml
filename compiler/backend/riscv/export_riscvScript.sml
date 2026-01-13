(*
  Define the format of the compiler-generated .S file for RISC-V
*)
Theory export_riscv
Ancestors
  export
Libs
  preamble

(*
CakeML expects 4 arguments in order:

a0 - entry address i.e., the address of cake_main
a1 - first address of heap
a2 - first address of stack
a3 - first address past the stack

In addition, the first address on the heap should store the address of cake_bitmaps

Note: this set up does NOT account for restoring clobbered registers
*)
Definition startup_def:
  startup ret pk =
    SmartAppend (List
      [strlit"\n";
       strlit"#### Start up code\n";
       strlit"\n";
       strlit"     .text\n";
       strlit"     .p2align 3\n";
       strlit"     .globl  cdecl(cml_main)\n";
       strlit"     .globl  cdecl(cml_heap)\n";
       strlit"     .globl  cdecl(cml_stack)\n";
       strlit"     .globl  cdecl(cml_stackend)\n";
       strlit"     .type   cml_main, function\n";
       strlit"cdecl(cml_main):\n";
       strlit"     la      a0,cake_main           # arg1: entry address\n";
       strlit"     ld      a1,cdecl(cml_heap)     # arg2: first address of heap\n"])
    (SmartAppend (List
      (if ~pk then
        [strlit"     la      t3,cake_bitmaps\n";
        strlit"     sd      t3, 0(a1)              # store bitmap pointer\n"]
      else []))
    (SmartAppend (List
      [strlit"     ld      a2,cdecl(cml_stack)    # arg3: first address of stack\n";
       strlit"     ld      a3,cdecl(cml_stackend) # arg4: first address past the stack\n"])
    (SmartAppend (List
      (if ret then
        [strlit"     j       cml_enter\n"]
      else
        [strlit"     j       cake_main\n"]))
    (List
      [strlit"\n"]))))
End

Definition ffi_asm_def:
  (ffi_asm [] = Nil) /\
  (ffi_asm (ffi::ffis) =
      SmartAppend (List [
       strlit"cake_ffi"; ffi; strlit":\n";
       strlit"     tail cdecl(ffi"; ffi; strlit")\n";
       strlit"     .p2align 4\n";
       strlit"\n"]) (ffi_asm ffis))
End

val ffi_code' =
  ``λret. SmartAppend
    (List (MAP (\n. strlit(n ++ "\n"))
     ["#### CakeML FFI interface (each block is 16 bytes long)";
       "";
       "     .p2align 4";
       ""]))(
    SmartAppend
     (ffi_asm (REVERSE ffi_names))
     (List (MAP (\n. strlit(n ++ "\n"))
      (["cake_clear:";
       "     tail cdecl(cml_exit)";
       "     .p2align 4";
       "";
       "cake_exit:"] ++
       (if ret then
         ["     j    cml_return"]
       else
         ["     tail cdecl(cml_exit)"]) ++
       ["     .p2align 4";
       "";
       "cake_main:";
       "";
       "#### Generated machine code follows";
       ""]))))``

val (ffi_code_true,ffi_code_false) =
    (``^ffi_code' T`` |> EVAL |> concl |> rand,
     ``^ffi_code' F`` |> EVAL |> concl |> rand);

val ffi_code =
  ``λret. if ret then ^ffi_code_true else ^ffi_code_false``;

val entry_point_code =
  ``(List (MAP (\n. strlit(n ++ "\n"))
    [""; "";
     "cml_enter:";
     "     addi    sp, sp, -32";
     "     sd      ra, 24(sp)";
     "     sd      s10, 16(sp)";
     "     sd      s9, 8(sp)";
     "     sd      s8, 0(sp)";
     "     j       cake_main";
     "     .p2align 4";
     ""; "";
     "cake_enter:";
     "     addi    sp, sp, -32";
     "     sd      ra, 24(sp)";
     "     sd      s10, 16(sp)";
     "     sd      s9, 8(sp)";
     "     sd      s8, 0(sp)";
     "     la      t1, can_enter";
     "     ld      t2, 0(t1)";
     "     beq     t2, zero, cake_err3";
     "     sd      zero, 0(t1)";
     "     la      t1, ret_base";
     "     ld      s10, 0(t1)";
     "     la      t1, ret_stack";
     "     ld      s8, 0(t1)";
     "     la      t1, ret_stackend";
     "     ld      s9, 0(t1)";
     "     la      ra, cake_return";
     "     jr      t0";
     "     .p2align 4";
     ""; "";
     "cml_return:";
     "     la      t1, ret_base";
     "     sd      s10, 0(t1)";
     "     la      t1, ret_stack";
     "     sd      s8, 0(t1)";
     "     la      t1, ret_stackend";
     "     sd      s9, 0(t1)";
     "";
     "cake_return:";
     "     la      t1, can_enter";
     "     li      t2, 1";
     "     sd      t2, 0(t1)";
     "     ld      s8, 0(sp)";
     "     ld      s9, 8(sp)";
     "     ld      s10, 16(sp)";
     "     ld      ra, 24(sp)";
     "     addi    sp, sp, 32";
     "     ret";
     "     .p2align 4";
     ""; "";
     "cake_err3:";
     "     li      a0, 3";
     "     j       cdecl(cml_err)";
     "     .p2align 4";
     ""]))`` |> EVAL |> concl |> rand;

Definition export_func_def:
  export_func appl (name,label,start,len) =
    SmartAppend appl (List
    [strlit"\n     .globl  cdecl("; name; strlit")\n";
     strlit"     .type   "; name; strlit", function\n";
     strlit"cdecl("; name; strlit"):\n";
     strlit"     la      t0, "; name; strlit"_jmp\n";
     strlit"     j       cake_enter\n";
            name; strlit"_jmp:\n";
     strlit"     j       "; label; strlit"\n"
    ])
End

Definition export_funcs_def:
  export_funcs lsyms exp =
    FOLDL export_func misc$Nil (FILTER ((flip MEM exp) o FST) lsyms)
End

Definition riscv_export_def:
  riscv_export ffi_names bytes (data:word64 list) syms exp ret pk =
    let lsyms = get_sym_labels syms in
    SmartAppend
      (SmartAppend (List preamble)
      (SmartAppend (List (data_section ".quad" ret))
      (SmartAppend (split16 (words_line (strlit"\t.quad ") word_to_string) data)
      (SmartAppend (List data_buffer)
      (SmartAppend (startup ret pk) (^ffi_code ret))))))
      (SmartAppend (split16 (words_line (strlit"\t.byte ") byte_to_string) bytes)
      (SmartAppend (List code_buffer)
      (SmartAppend (emit_symbols lsyms)
      (if ret then
        (SmartAppend ^entry_point_code (export_funcs lsyms exp))
      else List []))))
End
