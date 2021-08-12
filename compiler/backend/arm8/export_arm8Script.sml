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
val startup =
  ``(MAP (\n. strlit(n ++ "\n"))
      ["/* Start up code */";
       "";
       "     .text";
       "     .p2align 3";
       "     .globl  cdecl(cml_main)";
       "     .globl  cdecl(cml_heap)";
       "     .globl  cdecl(cml_stack)";
       "     .globl  cdecl(cml_stackend)";
       "#ifndef __APPLE__";
       "     .type   cml_main, function";
       "#endif";
       "";
       ".macro _ldrel reg sym";
       "#ifdef __APPLE__";
       "adrp \\reg, \\sym@PAGE";
       "add  \\reg, \\reg, \\sym@PAGEOFF";
       "#else";
       "adrp \\reg, \\sym";
       "add  \\reg, \\reg, :lo12:\\sym";
       "#endif";
       ".endm";
       "";
       "cdecl(cml_main):";
       "     _ldrel x0, cake_main            /* arg1: entry address */";
       "     _ldrel x1, cdecl(cml_heap)      /* arg2: first address of heap */";
       "     ldr    x1,[x1]";
       "     _ldrel x2, cake_bitmaps";
       "     str    x2,[x1]                  /* store bitmap pointer */";
       "     _ldrel x2, cdecl(cml_stack)     /* arg3: first address of stack */";
       "     ldr    x2,[x2]";
       "     _ldrel x3, cdecl(cml_stackend)  /* arg4: first address past the stack */";
       "     ldr    x3,[x3]";
       "     b      cake_main";
       "     .ltorg";
       ""])`` |> EVAL |> concl |> rand

val ffi_asm_def = Define `
  (ffi_asm [] = Nil) /\
  (ffi_asm (ffi::ffis) =
      SmartAppend (List [
       strlit"cake_ffi"; implode ffi; strlit":\n";
       strlit"     b     cdecl(ffi"; implode ffi; strlit")\n";
       strlit"     .p2align 4\n";
       strlit"\n"]) (ffi_asm ffis))`

val ffi_code =
  ``SmartAppend
    (List (MAP (\n. strlit(n ++ "\n"))
     ["/* CakeML FFI interface (each block is 16 bytes long) */";
       "";
       "     .p2align 4";
       ""]))(
    SmartAppend
     (ffi_asm (REVERSE ffi_names))
     (List (MAP (\n. strlit(n ++ "\n"))
      ["cake_clear:";
       "     b   cdecl(cml_exit)";
       "     .p2align 4";
       "";
       "cake_exit:";
       "     b   cdecl(cml_exit)";
       "     .p2align 4";
       "";
       "cake_main:";
       "";
       "/* Generated machine code follows */";
       ""])))`` |> EVAL |> concl |> rand

val arm8_export_def = Define `
  arm8_export ffi_names bytes (data:word64 list) syms =
    SmartAppend
      (SmartAppend (List preamble)
      (SmartAppend (List (data_section ".quad"))
      (SmartAppend (split16 (words_line (strlit"\t.quad ") word_to_string) data)
      (SmartAppend (List ((strlit"\n")::^startup)) ^ffi_code))))
      (SmartAppend (split16 (words_line (strlit"\t.byte ") byte_to_string) bytes)
      (emit_symbols syms))`;

val _ = export_theory ();
