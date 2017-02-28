open preamble mlstringTheory mlvectorTheory;

val () = new_theory "export_x64";

val byte_to_string_def = Define `
  byte_to_string (b:word8) =
    strlit ("0x" ++ [EL (w2n b DIV 16) "0123456789ABCDEF"]
                 ++ [EL (w2n b MOD 16) "0123456789ABCDEF"])`;

val all_bytes_def = Define `
  all_bytes = Vector (GENLIST (\n. byte_to_string (n2w n)) 256)`;

val all_bytes_eq = save_thm("all_bytes_eq",EVAL ``all_bytes``);

val byte_to_string_eq = store_thm("byte_to_string_eq",
  ``!b. byte_to_string b = sub all_bytes (w2n b)``,
  Cases_on `b` \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ rewrite_tac [all_bytes_def,mlvectorTheory.sub_def]
  \\ full_simp_tac std_ss [w2n_n2w,EVAL ``dimword (:8)``]
  \\ full_simp_tac std_ss [listTheory.EL_GENLIST]);

val comma_cat_def = Define `
  comma_cat x =
    case x of
    | [] => strlit ""
    | [x] => byte_to_string x
    | (x::xs) => strcat (byte_to_string x) (strcat (strlit ",") (comma_cat xs))`

val bytes_row_def = Define `
  bytes_row xs =
    List [strlit "\t.byte "; comma_cat xs; strlit "\n"]`;

val split16_def = tDefine "split16" `
  (split16 [] = Nil) /\
  (split16 xs =
     let xs1 = TAKE 16 xs in
     let xs2 = DROP 16 xs in
       SmartAppend (bytes_row xs1) (split16 xs2))`
  (WF_REL_TAC `measure LENGTH`
   \\ fs [listTheory.LENGTH_DROP]);

val num_to_str_def = Define `
  num_to_str n = if n < 10 then [CHR (48 + n)]
                 else (num_to_str (n DIV 10)) ++ ([CHR (48 + (n MOD 10))])`;

val num_to_str_ind = fetch "-" "num_to_str_ind";

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
        "cake_end:"; ""])``
      |> (PATH_CONV"r" EVAL THENC
          PATH_CONV"lrlrr" EVAL THENC
          PATH_CONV"lrlrlrlr" EVAL)
      |> concl |> rand

val startup =
  ``(MAP (\n. strlit(n ++ "\n"))
      ["#### Start up code";
       "";
       "     .text";
       "     .globl  cdecl(main)";
       "     .globl  cdecl(argc)";
       "     .globl  cdecl(argv)";
       "cdecl(main):";
       "     movq    %rdi, argc  # %rdi stores argc";
       "     movq    %rsi, argv  # %rsi stores argv";
       "     pushq   %rbp        # push base pointer";
       "     movq    %rsp, %rbp  # save stack pointer";
       "     leaq    cake_main(%rip), %rdi   # arg1: entry address";
       "     leaq    cake_heap(%rip), %rsi   # arg2: first address of heap";
       "     leaq    cake_stack(%rip), %rbx  # arg3: first address of stack";
       "     leaq    cake_end(%rip), %rdx    # arg4: first address past the stack";
       "     jmp     cake_main";
       "";
       "     .data";
       "argc:  .quad 0";
       "argv:  .quad 0";
       ""])`` |> EVAL |> concl |> rand

val ffi_asm_def = Define `
  ffi_asm [] = Nil /\
  ffi_asm (ffi::ffis) =
      SmartAppend (List [
       strlit"cake_ffi"; implode ffi; strlit":\n";
       strlit"     pushq   %rax\n";
       strlit"     jmp     cdecl(ffi"; implode ffi; strlit")\n";
       strlit"     .p2align 3\n";
       strlit"\n"]) (ffi_asm ffis)`

val ffi_code =
  ``SmartAppend
    (List (MAP (\n. strlit(n ++ "\n"))
     ["#### CakeML FFI interface (each block is 8 bytes long)";
       "";
       "     .p2align 3";
       ""]))(
    SmartAppend
     (ffi_asm (REVERSE ffi_names))
     (List (MAP (\n. strlit(n ++ "\n"))
      ["cake_clear:";
       "     callq   cdecl(exit)";
       "     .p2align 3";
       "";
       "cake_exit:";
       "     callq   cdecl(exit)";
       "     .p2align 3";
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

val _ = export_theory ();
