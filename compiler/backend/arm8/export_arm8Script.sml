(*
  Define the format of the compiler-generated .S file for ARMv8
*)
open preamble exportTheory

val () = new_theory "export_arm8";

val startup =
  ``(MAP (\n. implode(n ++ "\n"))
      ["/* Start up code */";
       "";
       "     .text";
       "     .p2align 3";
       "     .globl  cdecl(main)";
       "     .globl  cdecl(argc)";
       "     .globl  cdecl(argv)";
       "cdecl(main):";
       "     ldr    x2,=cdecl(argc)";
       "     ldr    x3,=cdecl(argv)";
       "     str    x0,[x2]";
       "     str    x1,[x3]";
       "     ldr    x0,=cake_main";
       "     ldr    x1,=cake_heap";
       "     ldr    x2,=cake_bitmaps";
       "     str    x2,[x1]";
       "     ldr    x2,=cake_stack";
       "     ldr    x3,=cake_end";
       "     b      cake_main";
       "     .ltorg";
       ""])`` |> EVAL |> concl |> rand

val ffi_asm_def = Define `
  (ffi_asm [] = Nil) /\
  (ffi_asm (ffi::ffis) =
      SmartAppend (List [
       implode"cake_ffi"; implode ffi; implode":\n";
       implode"     b     cdecl(ffi"; implode ffi; implode")\n";
       implode"     .p2align 4\n";
       implode"\n"]) (ffi_asm ffis))`

val ffi_code =
  ``SmartAppend
    (List (MAP (\n. implode(n ++ "\n"))
     ["/* CakeML FFI interface (each block is 16 bytes long) */";
       "";
       "     .p2align 4";
       ""]))(
    SmartAppend
     (ffi_asm (REVERSE ffi_names))
     (List (MAP (\n. implode(n ++ "\n"))
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
  arm8_export ffi_names heap_space stack_space bytes (data:word64 list) =
    SmartAppend
      (SmartAppend (List preamble)
      (SmartAppend (List (data_section ".quad" heap_space stack_space))
      (SmartAppend (split16 (words_line (implode"\t.quad ") word_to_string) data)
      (SmartAppend (List ((implode"\n")::^startup)) ^ffi_code))))
      (split16 (words_line (implode"\t.byte ") byte_to_string) bytes)`;

val _ = export_theory ();
