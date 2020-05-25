(*
  Define the format of the compiler-generated .S file for ARMv7
*)
open preamble exportTheory

val () = new_theory "export_arm7";

(*
CakeML expects 4 arguments in order:

r0 - entry address i.e., the address of cake_main
r1 - first address of heap
r2 - first address of stack
r3 - first address past the stack

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
       "     .globl  cdecl(heap)";
       "     .globl  cdecl(stack)";
       "     .globl  cdecl(stackend)";
       "cdecl(cml_main):";
       "     ldr    r0,=cake_main        /* arg1: entry address */";
       "     ldr    r1,=cdecl(heap)      /* arg2: first address of heap */";
       "     ldr    r2,=cake_bitmaps";
       "     str    r2,[r1]              /* store bitmap pointer */";
       "     ldr    r2,=cdecl(stack)     /* arg3: first address of stack */";
       "     ldr    r3,=cdecl(stakend)   /* arg4: first address past the stack */ ";
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
  arm7_export ffi_names bytes (data:word32 list) =
    SmartAppend
      (SmartAppend (List preamble)
      (SmartAppend (List (data_section ".long"))
      (SmartAppend (split16 (words_line (strlit"\t.long ") word_to_string) data)
      (SmartAppend (List ((strlit"\n")::^startup)) ^ffi_code))))
      (split16 (words_line (strlit"\t.byte ") byte_to_string) bytes)`;

val _ = export_theory ();
