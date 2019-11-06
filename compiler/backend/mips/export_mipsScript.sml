(*
  Define the format of the compiler-generated .S file for MIPS
*)
open preamble exportTheory

val () = new_theory "export_mips";

val startup =
  ``(MAP (\n. implode(n ++ "\n"))
      ["#### Start up code";
       "";
       "     .text";
       "     .p2align 3";
       "     .globl  cdecl(main)";
       "     .globl  cdecl(argc)";
       "     .globl  cdecl(argv)";
       "";
       "cdecl(main):";
       "     dla     $t0,cdecl(argc)";
       "     dla     $t1,cdecl(argv)";
       "     sd      $a0, 0($t0)      # a0 stores argc";
       "     sd      $a1, 0($t1)      # a1 stores argv";
       "     dla     $a0,cake_main   # arg1: entry address";
       "     dla     $a1,cake_heap   # arg2: first address of heap";
       "     dla     $t0,cake_bitmaps";
       "     sd      $t0, 0($a1)      # store bitmap pointer";
       "     dla     $a2,cake_stack  # arg3: first address of stack";
       "     dla     $a3,cake_end    # arg4: first address past the stack";
       "     j       cake_main";
       "     nop";
       ""])`` |> EVAL |> concl |> rand

val ffi_asm_def = Define `
  (ffi_asm [] = Nil) /\
  (ffi_asm (ffi::ffis) =
      SmartAppend (List [
       implode"cake_ffi"; implode ffi; implode":\n";
       implode"     dla    $t9,cdecl(ffi"; implode ffi; implode")\n";
       implode"     jr     $t9\n";
       implode"     .p2align 4\n";
       implode"\n"]) (ffi_asm ffis))`

val ffi_code =
  ``SmartAppend
    (List (MAP (\n. implode(n ++ "\n"))
     ["#### CakeML FFI interface (each block is 16 bytes long)";
       "";
       "     .p2align 4";
       ""]))(
    SmartAppend
     (ffi_asm (REVERSE ffi_names))
     (List (MAP (\n. implode(n ++ "\n"))
      ["cake_clear:";
       "     dla   $t9,cdecl(cml_exit)";
       "     jr    $t9";
       "     .p2align 4";
       "";
       "cake_exit:";
       "     dla   $t9,cdecl(cml_exit)";
       "     jr    $t9";
       "     .p2align 4";
       "";
       "cake_main:";
       "";
       "#### Generated machine code follows";
       ""])))`` |> EVAL |> concl |> rand

val mips_export_def = Define `
  mips_export ffi_names heap_space stack_space bytes (data:word64 list) =
    SmartAppend
      (SmartAppend (List preamble)
      (SmartAppend (List (data_section ".quad" heap_space stack_space))
      (SmartAppend (split16 (words_line (implode"\t.quad ") word_to_string) data)
      (SmartAppend (List ((implode"\n")::^startup)) ^ffi_code))))
      (split16 (words_line (implode"\t.byte ") byte_to_string) bytes)`;

val _ = export_theory ();
