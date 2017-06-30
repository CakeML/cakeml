open preamble exportTheory

val () = new_theory "export_x64";

val preamble =
  ``(MAP (\n. strlit(n ++ "\n"))
      ["#### Preprocessor to get around Mac OS and Linux differences in naming";
       "";
       "#if defined(__APPLE__)";
       "# define cdecl(s) _##s";
       "#else";
       "# define cdecl(s) s";
       "#endif";
       "";
       "     .file        \"cake.S\"";
       ""])`` |> EVAL |> concl |> rand

val heap_stack_space =
  `` (MAP (\n. strlit (n ++ "\n"))
       ["#### Data section -- modify the numbers to change stack/heap size";
        "";
        "     .bss";
        "     .p2align 3";
        "cake_heap:"] ++
      [implode("     .space 1024 * 1024 * " ++ num_to_str heap_space ++ "\n")] ++
      MAP (\n. strlit (n ++ "\n"))
       ["     .p2align 3";
        "cake_stack:"] ++
      [implode("     .space 1024 * 1024 * " ++ num_to_str stack_space ++ "\n")] ++
      MAP (\n. (strlit (n ++ "\n")))
       ["     .p2align 3";
        "cake_end:";
        "";
        "     .data";
        "     .p2align 3";
        "cdecl(argc): .quad 0";
        "cdecl(argv): .quad 0";
        ""])``
      |> (PATH_CONV"r" EVAL THENC
          PATH_CONV"lrlrr" EVAL THENC
          PATH_CONV"lrlrlrlr" EVAL)
      |> concl |> rand

val startup =
  ``(MAP (\n. strlit(n ++ "\n"))
      ["#### Start up code";
       "";
       "     .text";
       "     .p2align 3";
       "     .globl  cdecl(main)";
       "     .globl  cdecl(argc)";
       "     .globl  cdecl(argv)";
       "cdecl(main):";
       "     leaq    cdecl(argc)(%rip), %rbx";
       "     leaq    cdecl(argv)(%rip), %rdx";
       "     movq    %rdi, 0(%rbx)  # %rdi stores argc";
       "     movq    %rsi, 0(%rdx)  # %rsi stores argv";
       "     pushq   %rbp        # push base pointer";
       "     movq    %rsp, %rbp  # save stack pointer";
       "     leaq    cake_main(%rip), %rdi   # arg1: entry address";
       "     leaq    cake_heap(%rip), %rsi   # arg2: first address of heap";
       "     leaq    cake_stack(%rip), %rbx  # arg3: first address of stack";
       "     leaq    cake_end(%rip), %rdx    # arg4: first address past the stack";
       "     jmp     cake_main";
       ""])`` |> EVAL |> concl |> rand

val ffi_asm_def = Define `
  (ffi_asm [] = Nil) /\
  (ffi_asm (ffi::ffis) =
      SmartAppend (List [
       strlit"cake_ffi"; implode ffi; strlit":\n";
       strlit"     pushq   %rax\n";
       strlit"     jmp     cdecl(ffi"; implode ffi; strlit")\n";
       strlit"     .p2align 4\n";
       strlit"\n"]) (ffi_asm ffis))`

val ffi_code =
  ``SmartAppend
    (List (MAP (\n. strlit(n ++ "\n"))
     ["#### CakeML FFI interface (each block is 16 bytes long)";
       "";
       "     .p2align 3";
       ""]))(
    SmartAppend
     (ffi_asm (REVERSE ffi_names))
     (List (MAP (\n. strlit(n ++ "\n"))
      ["cake_clear:";
       "     callq   cdecl(exit)";
       "     .p2align 4";
       "";
       "cake_exit:";
       "     callq   cdecl(exit)";
       "     .p2align 4";
       "";
       "cake_main:";
       "";
       "#### Generated machine code follows";
       ""])))`` |> EVAL |> concl |> rand

val x64_export_def = Define `
  x64_export ffi_names heap_space stack_space bytes =
    SmartAppend
      (SmartAppend (List ^preamble)
      (SmartAppend (List ^heap_stack_space)
      (SmartAppend (List ^startup) ^ffi_code)))
      (split16 bytes)`;

(*
  EVAL ``append (x64_export ["getArgs";"putChar";"getChar"] 400 300 [3w;4w;5w])``
  |> concl |> rand |> listSyntax.dest_list |> fst |> map rand
  |> map stringSyntax.fromHOLstring |> concat |> print
*)

val _ = export_theory ();
