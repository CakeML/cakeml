(*
  Define the format of the compiler-generated .S file for RISC-V
*)
open preamble exportTheory

val () = new_theory "export_riscv";

(*
CakeML expects 4 arguments in order:

a0 - entry address i.e., the address of cake_main
a1 - first address of heap
a2 - first address of stack
a3 - first address past the stack

In addition, the first address on the heap should store the address of cake_bitmaps

Note: this set up does NOT account for restoring clobbered registers
*)
val startup =
  ``(MAP (\n. strlit(n ++ "\n"))
      ["#### Start up code";
       "";
       "     .text";
       "     .p2align 3";
       "     .globl  cdecl(cml_main)";
       "     .globl  cdecl(cml_heap)";
       "     .globl  cdecl(cml_stack)";
       "     .globl  cdecl(cml_stackend)";
       "cdecl(cml_main):";
       "     la      a0,cake_main           # arg1: entry address";
       "     la      a1,cdecl(cml_heap)     # arg2: first address of heap";
       "     la      t3,cake_bitmaps";
       "     sd      t3, 0(a1)              # store bitmap pointer";
       "     la      a2,cdecl(cml_stack)    # arg3: first address of stack";
       "     la      a3,cdecl(cml_stackend) # arg4: first address past the stack";
       "     j       cake_main";
       ""])`` |> EVAL |> concl |> rand

val ffi_asm_def = Define `
  (ffi_asm [] = Nil) /\
  (ffi_asm (ffi::ffis) =
      SmartAppend (List [
       strlit"cake_ffi"; implode ffi; strlit":\n";
       strlit"     la     t6,cdecl(ffi"; implode ffi; strlit")\n";
       strlit"     jr     t6\n";
       strlit"     .p2align 4\n";
       strlit"\n"]) (ffi_asm ffis))`

val ffi_code =
  ``SmartAppend
    (List (MAP (\n. strlit(n ++ "\n"))
     ["#### CakeML FFI interface (each block is 16 bytes long)";
       "";
       "     .p2align 4";
       ""]))(
    SmartAppend
     (ffi_asm (REVERSE ffi_names))
     (List (MAP (\n. strlit(n ++ "\n"))
      ["cake_clear:";
       "     la   t6,cdecl(cml_exit)";
       "     jr   t6";
       "     .p2align 4";
       "";
       "cake_exit:";
       "     la   t6,cdecl(cml_exit)";
       "     jr   t6";
       "     .p2align 4";
       "";
       "cake_main:";
       "";
       "#### Generated machine code follows";
       ""])))`` |> EVAL |> concl |> rand

val riscv_export_def = Define `
  riscv_export ffi_names bytes (data:word64 list) =
    SmartAppend
      (SmartAppend (List preamble)
      (SmartAppend (List (data_section ".quad"))
      (SmartAppend (split16 (words_line (strlit"\t.quad ") word_to_string) data)
      (SmartAppend (List ((strlit"\n")::^startup)) ^ffi_code))))
      (split16 (words_line (strlit"\t.byte ") byte_to_string) bytes)`;

val _ = export_theory ();
