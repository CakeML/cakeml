(*
  Define the format of the compiler-generated .S file for ARMv7
*)
open preamble exportTheory

val () = new_theory "export_arm7";

val startup =
  ``(MAP (\n. strlit(n ++ "\n"))
      ["/* Start up code */";
       "";
       "     .text";
       "     .p2align 3";
       "     .globl  cdecl(main)";
       "     .globl  cdecl(argc)";
       "     .globl  cdecl(argv)";
       "cdecl(main):";
       "     ldr    r2,=cdecl(argc)";
       "     ldr    r3,=cdecl(argv)";
       "     str    r0,[r2]";
       "     str    r1,[r3]";
       "     ldr    r0,=cake_main";
       "     ldr    r1,=cake_heap";
       "     ldr    r2,=cake_bitmaps";
       "     str    r2,[r1]";
       "     ldr    r2,=cake_stack";
       "     ldr    r3,=cake_end";
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

val arm7_export_def = Define `
  arm7_export ffi_names heap_space stack_space bytes (data:word32 list) =
    SmartAppend
      (SmartAppend (List preamble)
      (SmartAppend (List (data_section ".long" heap_space stack_space))
      (SmartAppend (split16 (words_line (strlit"\t.long ") word_to_string) data)
      (SmartAppend (List ((strlit"\n")::^startup)) ^ffi_code))))
      (split16 (words_line (strlit"\t.byte ") byte_to_string) bytes)`;

val _ = export_theory ();
