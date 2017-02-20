open preamble mlstringTheory;

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
    strcat (strcat (strlit "\t.byte ") (comma_cat xs)) (strlit "\n")`;

val split16_def = tDefine "split16" `
  (split16 [] = strlit "") /\
  (split16 xs =
     let xs1 = TAKE 16 xs in
     let xs2 = DROP 16 xs in
       strcat (bytes_row xs1) (split16 xs2))`
  (WF_REL_TAC `measure LENGTH`
   \\ fs [listTheory.LENGTH_DROP]);

val num_to_str_def = Define `
  num_to_str n = if n < 10 then [CHR (48 + n)]
                 else (num_to_str (n DIV 10)) ++ ([CHR (48 + (n MOD 10))])`;

val num_to_str_ind = fetch "-" "num_to_str_ind";

val preamble =
  ``(MAP (\n. n ++ "\n")
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
  `` (MAP (\n. n ++ "\n")
       ["#### Data section -- modify the numbers to change stack/heap size";
        "";
        "     .bss";
        "     .p2align 3";
        "cake_heap:"] ++
      ["     .space 1024 * 1024 * " ++ num_to_str heap_space ++ "\n"] ++
      MAP (\n. n ++ "\n")
       ["     .p2align 3";
        "cake_stack:"] ++
      ["     .space 1024 * 1024 * " ++ num_to_str stack_space ++ "\n"] ++
      MAP (\n. n ++ "\n")
       ["     .p2align 3";
        "cake_end:"; ""])``

val startup =
  ``(MAP (\n. n ++ "\n")
      ["#### Start up code";
       "";
       "     .text";
       "     .globl  cdecl(main)";
       "cdecl(main):";
       "     pushq   %rbp        # push base pointer";
       "     movq    %rsp, %rbp  # save stack pointer";
       "     leaq    cake_main(%rip), %rdi   # arg1: entry address";
       "     leaq    cake_heap(%rip), %rsi   # arg2: first address of heap";
       "     leaq    cake_stack(%rip), %rbx  # arg3: first address of stack";
       "     leaq    cake_end(%rip), %rdx    # arg4: first address past the stack";
       "     jmp     cake_main";
       ""])`` |> EVAL |> concl |> rand

val ffi_asm_def = Define `
  ffi_asm [] = [] /\
  ffi_asm (ffi::ffis) =
      ("cake_ffi" ++ ffi ++ ":\n") ::
       "     pushq   %rax\n"::
       ("     jmp     cdecl(ffi" ++ ffi ++ ")\n")::
       "     .p2align 3\n"::
       "\n":: ffi_asm ffis`

val ffi_code =
  ``(MAP (\n. n ++ "\n")
     ["#### CakeML FFI interface (each block is 8 bytes long)";
       "";
       "     .p2align 3";
       ""] ++
     ffi_asm (REVERSE ffi_names) ++
     MAP (\n. n ++ "\n")
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
       ""])`` |> EVAL |> concl |> rand

val x64_export_def = Define `
  x64_export ffi_names heap_space stack_space bytes =
    strcat (implode (FLAT (^preamble ++
                           ^heap_stack_space ++
                           ^startup ++ ^ffi_code)))
           (split16 bytes)`

val _ = export_theory ();
