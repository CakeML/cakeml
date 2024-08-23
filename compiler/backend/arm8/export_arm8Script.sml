(*
  Define the format of the compiler-generated .S file for ARMv8
*)
open preamble exportTheory

val () = new_theory "export_arm8";

(*
CakeML expects 4 arguments in order:

x0 - entry address i.e., the address of cake_main
x1 - first address of heap
x2 - first address of stack
x3 - first address past the stack

In addition, the first address on the heap should store the address of cake_bitmaps

Note: this set up does NOT account for restoring clobbered registers
*)
val startup_def = Define `
  startup ret pk =
    SmartAppend (List
      [strlit"\n";
       strlit"/* Start up code */\n";
       strlit"\n";
       strlit"     .text\n";
       strlit"     .p2align 3\n";
       strlit"     .globl  cdecl(cml_main)\n";
       strlit"     .globl  cdecl(cml_heap)\n";
       strlit"     .globl  cdecl(cml_stack)\n";
       strlit"     .globl  cdecl(cml_stackend)\n";
       strlit"#ifndef __APPLE__\n";
       strlit"     .type   cml_main, function\n";
       strlit"#endif\n";
       strlit"\n";
       strlit".macro _ldrel reg sym\n";
       strlit"#ifdef __APPLE__\n";
       strlit"adrp \\reg, \\sym@PAGE\n";
       strlit"add  \\reg, \\reg, \\sym@PAGEOFF\n";
       strlit"#else\n";
       strlit"adrp \\reg, \\sym\n";
       strlit"add  \\reg, \\reg, :lo12:\\sym\n";
       strlit"#endif\n";
       strlit".endm\n";
       strlit"\n";
       strlit"cdecl(cml_main):\n";
       strlit"     _ldrel x0, cake_main            /* arg1: entry address */\n";
       strlit"     _ldrel x1, cdecl(cml_heap)      /* arg2: first address of heap */\n";
       strlit"     ldr    x1,[x1]\n"])
    (SmartAppend (List
      (if ~pk then
        [strlit"     _ldrel x2, cake_bitmaps\n";
         strlit"     str    x2,[x1]                  /* store bitmap pointer */\n"]
      else []))
    (SmartAppend (List
      [strlit"     _ldrel x2, cdecl(cml_stack)     /* arg3: first address of stack */\n";
       strlit"     ldr    x2,[x2]\n";
       strlit"     _ldrel x3, cdecl(cml_stackend)  /* arg4: first address past the stack */\n";
       strlit"     ldr    x3,[x3]\n"])
    (SmartAppend (List
      (if ret then
        [strlit"     b      cml_enter\n"]
      else
        [strlit"     b      cake_main\n"]))
    (List
      [strlit"     .ltorg\n";
       strlit"\n"]))))`

val ffi_asm_def = Define `
  (ffi_asm [] = Nil) /\
  (ffi_asm (ffi::ffis) =
      SmartAppend (List [
       strlit"cake_ffi"; implode ffi; strlit":\n";
       strlit"     b     cdecl(ffi"; implode ffi; strlit")\n";
       strlit"     .p2align 4\n";
       strlit"\n"]) (ffi_asm ffis))`

val ffi_code' =
  ``λret. SmartAppend
    (List (MAP (\n. strlit(n ++ "\n"))
     ["/* CakeML FFI interface (each block is 16 bytes long) */";
       "";
       "     .p2align 4";
       ""]))(
    SmartAppend
     (ffi_asm (REVERSE ffi_names))
     (List (MAP (\n. strlit(n ++ "\n"))
      (["cake_clear:";
       "     b   cdecl(cml_exit)";
       "     .p2align 4";
       "";
       "cake_exit:"] ++
       (if ret then
         ["     b   cml_return"]
       else
         ["     b   cdecl(cml_exit)"]) ++
       ["     .p2align 4";
       "";
       "cake_main:";
       "";
       "/* Generated machine code follows */";
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
     "     str    x30, [sp, #-32]!";
     "     str    x28, [sp, #-32]!";
     "     str    x27, [sp, #-32]!";
     "     str    x25, [sp, #-32]!";
     "     b      cake_main";
     "     .p2align 4";
     ""; "";
     "cake_enter:";
     "     str    x30, [sp, #-32]!";
     "     str    x28, [sp, #-32]!";
     "     str    x27, [sp, #-32]!";
     "     str    x25, [sp, #-32]!";
     "     _ldrel x9, can_enter";
     "     ldr    x11, [x9]";
     "     cbz    x11, cake_err3";
     "     str    xzr, [x9]";
     "     _ldrel x9, ret_base";
     "     ldr    x28, [x9]";
     "     _ldrel x9, ret_stack";
     "     ldr    x25, [x9]";
     "     _ldrel x9, ret_stackend";
     "     ldr    x27, [x9]";
     "     _ldrel x30, cake_return";
     "     br     x10";
     "     .p2align 4";
     ""; "";
     "cml_return:";
     "     _ldrel x9, ret_base";
     "     str    x28, [x9]";
     "     _ldrel x9, ret_stack";
     "     str    x25, [x9]";
     "     _ldrel x9, ret_stackend";
     "     str    x27, [x9]";
     "";
     "cake_return:";
     "     _ldrel x9, can_enter";
     "     mov    x11, #1";
     "     str    x11, [x9]";
     "     mov    x8, x0";
     "     ldr    x25, [sp], #32";
     "     ldr    x27, [sp], #32";
     "     ldr    x28, [sp], #32";
     "     ldr    x30, [sp], #32";
     "     ret";
     "     .p2align 4";
     ""; "";
     "cake_err3:";
     "     mov    x0, #3";
     "     b      cdecl(cml_err)";
     "     .p2align 4";
     ""]))`` |> EVAL |> concl |> rand;

val export_func_def = Define `
  export_func appl (name,label,start,len) =
    SmartAppend appl (List
    [strlit"\n    .globl cdecl("; name; strlit")\n";
     strlit"#ifndef __APPLE__\n";
     strlit"     .type   "; name; strlit", function\n";
     strlit"#endif\n";
     strlit"cdecl("; name; strlit"):\n";
     strlit"     _ldrel x10, "; name; strlit"_jmp\n";
     strlit"     b      cake_enter\n";
            name; strlit"_jmp:\n";
     strlit"     b      "; label; strlit"\n"
    ])`;

val export_funcs_def = Define `
  export_funcs lsyms exp =
    FOLDL export_func misc$Nil (FILTER ((flip MEM exp) o FST) lsyms)`;

val arm8_export_def = Define `
  arm8_export ffi_names bytes (data:word64 list) syms exp ret pk =
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
      else List []))))`;



val _ = export_theory ();
