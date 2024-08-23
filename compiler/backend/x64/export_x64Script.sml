(*
  Define the format of the compiler-generated .S file for x64
*)
open preamble exportTheory

val () = new_theory "export_x64";

(*
CakeML expects 4 arguments in order:

RDI - entry address i.e., the address of cake_main
RSI - first address of heap
RDX - first address of stack
RCX - first address past the stack

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
       strlit"     .p2align 12\n";
       strlit"     .globl  cdecl(cake_text_begin)\n";
       strlit"cdecl(cake_text_begin):\n";
       strlit"     .globl  cdecl(cml_main)\n";
       strlit"     .globl  cdecl(cml_heap)\n";
       strlit"     .globl  cdecl(cml_stack)\n";
       strlit"     .globl  cdecl(cml_stackend)\n";
       strlit"#if defined(__APPLE__)\n";
       strlit"\n";
       strlit"#elif defined(__WIN32)\n";
       strlit"     .func   cml_main\n";
       strlit"#else\n";
       strlit"     .type   cml_main, function\n";
       strlit"#endif\n";
       strlit"cdecl(cml_main):\n";
       strlit"     pushq   %rbp                            # push base pointer\n";
       strlit"     movq    %rsp, %rbp                      # save stack pointer\n";
       strlit"     leaq    cake_main(%rip), %rdi           # arg1: entry address\n";
       strlit"     movq    cdecl(cml_heap)(%rip), %rsi     # arg2: first address of heap\n"])
    (SmartAppend (List
      (if ~pk then
        [strlit"     leaq    cake_bitmaps(%rip), %rax\n";
         strlit"     movq    %rax, 0(%rsi)                   # store bitmap pointer\n";
         strlit"     leaq    cdecl(cake_bitmaps_buffer_begin)(%rip), %rax\n";
         strlit"     movq    %rax, 8(%rsi)                   # store bitmap mutable start pointer\n";
         strlit"     leaq    cdecl(cake_bitmaps_buffer_end)(%rip), %rax\n";
         strlit"     movq    %rax, 16(%rsi)                  # store bitmap mutable end pointer\n";
         strlit"     leaq    cdecl(cake_codebuffer_begin)(%rip), %rax\n";
         strlit"     movq    %rax, 24(%rsi)                  # store code mutable start pointer\n";
         strlit"     leaq    cdecl(cake_codebuffer_end)(%rip), %rax\n";
         strlit"     movq    %rax, 32(%rsi)                  # store code mutable end pointer\n"]
      else []))
    (SmartAppend (List
      [strlit"     movq    cdecl(cml_stack)(%rip), %rdx    # arg3: first address of stack\n";
       strlit"     movq    cdecl(cml_stackend)(%rip), %rcx # arg4: first address past the stack\n"])
    (SmartAppend (List
      (if ret then
        [strlit"     jmp     cml_enter\n"]
      else
        [strlit"     jmp     cake_main\n"]))
    (List
      [strlit"\n";
       strlit"#if defined(__WIN32)\n";
       strlit"     .endfunc\n";
       strlit"#endif\n"]))))`

val ffi_asm_def = Define `
  (ffi_asm [] = Nil) /\
  (ffi_asm (ffi::ffis) =
      SmartAppend (List [
       strlit"cake_ffi"; implode ffi; strlit":\n";
       strlit"     pushq   %rax\n";
       strlit"     jmp     wcdecl(ffi"; implode ffi; strlit")\n";
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
       "     pushq   %rax";
       "     pushq   %rdi";
       "     callq   wcdecl(cml_clear)";
       "     popq    %rdi";
       "     ret";
       "     .p2align 4";
       "";
       "cake_exit:"] ++
       (if ret then
         ["     jmp     cml_return"]
       else
         ["     callq   cdecl(cml_exit)"]) ++
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

val windows_ffi_asm_def = Define `
  (windows_ffi_asm [] = Nil) /\
  (windows_ffi_asm (ffi::ffis) =
      SmartAppend (List [
       strlit"windows_ffi"; implode ffi; strlit":\n";
       strlit"     movq    %rcx, %r9\n";
       strlit"     movq    %rdx, %r8\n";
       strlit"     movq    %rsi, %rdx\n";
       strlit"     movq    %rdi, %rcx\n";
       strlit"     jmp     cdecl(ffi"; implode ffi; strlit")\n";
       strlit"\n"]) (windows_ffi_asm ffis))`

val windows_ffi_code' =
  ``λret. SmartAppend
    (
     List [strlit "\n/* Windows Compatibility for CakeML FFI interface */\n\n"]
    )
    (
    SmartAppend
     (windows_ffi_asm (REVERSE ffi_names))
     (List (MAP (\n. strlit(n ++ "\n"))
      (["windows_cml_clear:";
        "     movq    %rcx, %r9";
        "     movq    %rdx, %r8";
        "     movq    %rsi, %rdx";
        "     movq    %rdi, %rcx";
        "     jmp     cdecl(cml_clear)"] ++
       (if ret then (* don't need to treat cake_exit as a function *)
         []
       else
         ["windows_cml_exit:";
         "     movq    %rcx, %r9";
         "     movq    %rdx, %r8";
         "     movq    %rsi, %rdx";
         "     movq    %rdi, %rcx";
         "     callq   cdecl(cml_exit)"])))))``;

val (windows_ffi_code_true,windows_ffi_code_false) =
    (``^windows_ffi_code' T`` |> EVAL |> concl |> rand,
     ``^windows_ffi_code' F`` |> EVAL |> concl |> rand);

val windows_ffi_code =
  ``λret. if ret then ^windows_ffi_code_true else ^windows_ffi_code_false``;

val entry_point_code =
  ``(List (MAP (\n. strlit(n ++ "\n"))
    ["cml_enter:";
     "     sub     $0x30, %rsp";
     "     movq    %r12, -0x8(%rbp)";
     "     movq    %r13, -0x10(%rbp)";
     "     movq    %r14, -0x18(%rbp)";
     "     movq    %r15, -0x20(%rbp)";
     "     movq    %rbx, -0x28(%rbp)";
     "     jmp     cake_main";
     "";
     "windows_cake_enter:";
     "     movq    %rcx, %rdi";
     "     movq    %rdx, %rsi";
     "     movq    %r8, %rdx";
     "     movq    %r9, %rcx";
     "";
     "cake_enter:";
     "     pushq   %rbp";
     "     movq    %rsp, %rbp";
     "     sub     $0x30, %rsp";
     "     movq    %r12, -0x8(%rbp)";
     "     movq    %r13, -0x10(%rbp)";
     "     movq    %r14, -0x18(%rbp)";
     "     movq    %r15, -0x20(%rbp)";
     "     movq    %rbx, -0x28(%rbp)";
     "     movq    can_enter(%rip), %r11";
     "     cmp     $0, %r11";
     "     je      cake_err3";
     "     movq    $0, can_enter(%rip)";
     "     movq    ret_base(%rip), %r14";
     "     movq    ret_stack(%rip), %r12";
     "     movq    ret_stackend(%rip), %r13";
     "     lea     cake_return(%rip), %rax";
     "     jmp     *%r10";
     "     .p2align 4";
     "";
     "cml_return:";
     "     movq    %r14, ret_base(%rip)";
     "     movq    %r12, ret_stack(%rip)";
     "     movq    %r13, ret_stackend(%rip)";
     "";
     "cake_return:";
     "     movq    $1, can_enter(%rip)";
     "     mov     %edi, %eax";
     "     movq    -0x28(%rbp),%rbx";
     "     movq    -0x20(%rbp),%r15";
     "     movq    -0x18(%rbp),%r14";
     "     movq    -0x10(%rbp),%r13";
     "     movq    -0x8(%rbp),%r12";
     "     leave";
     "     ret";
     "     .p2align 4";
     "";
     "cake_err3:";
     "     pushq   %rax";
     "     movq    $3, %rdi";
     "     jmp     wcdecl(cml_err)";
     "     .p2align 4";
     "";
     "windows_cml_err:";
     "     movq    %rcx, %r9";
     "     movq    %rdx, %r8";
     "     movq    %rsi, %rdx";
     "     movq    %rdi, %rcx";
     "     jmp     cdecl(cml_err)";
     ""]))`` |> EVAL |> concl |> rand;

val export_func_def = Define `
  export_func appl (name,label,start,len) =
    SmartAppend appl (List
    [strlit"\n    .globl cdecl("; name; strlit")\n";
     strlit"#if defined(__APPLE__)\n";
     strlit"\n";
     strlit"#elif defined(__WIN32)\n";
     strlit"     .func   cdecl("; name; strlit")\n";
     strlit"#else\n";
     strlit"     .type   cdecl("; name; strlit"), function\n";
     strlit"#endif\n";
     strlit"cdecl("; name; strlit"):\n";
     strlit"     lea     "; name; strlit"_jmp(%rip), %r10\n";
     strlit"     jmp     wcml(cake_enter)\n";
            name; strlit"_jmp:\n";
     strlit"     jmp     "; label; strlit"\n";
     strlit"#if defined(__WIN32)\n";
     strlit"     .endfunc\n";
     strlit"#endif\n";
    ])`;

val export_funcs_def = Define `
  export_funcs lsyms exp =
    FOLDL export_func misc$Nil (FILTER ((flip MEM exp) o FST) lsyms)`;

val x64_export_def = Define `
  x64_export ffi_names bytes (data:word64 list) syms exp ret pk =
    let lsyms = get_sym_labels syms in
    SmartAppend
      (SmartAppend
      (SmartAppend (List preamble)
      (SmartAppend (List (data_section ".quad" ret))
      (SmartAppend (split16 (words_line (strlit"\t.quad ") word_to_string) data)
      (SmartAppend (List data_buffer)
      (SmartAppend (startup ret pk) (^ffi_code ret))))))
      (SmartAppend (split16 (words_line (strlit"\t.byte ") byte_to_string) bytes)
      (SmartAppend (List code_buffer)
      (emit_symbols lsyms))))
      (SmartAppend (^windows_ffi_code ret)
      (if ret then
        (SmartAppend ^entry_point_code (export_funcs lsyms exp))
      else List []))`;

(*
  EVAL``append(split16 (words_line (strlit"\t.quad ") word_to_string) [100w:word64;393w;392w])``

  EVAL ``append (x64_export ["getArgs";"putChar";"getChar"] 400 300
    [3w;4w;5w;9w;11w;12w;13w;14w;79w;12w;91w;21w;34w;32w;53w;255w;128w;122w;127w]
    [0w;3w;2w;9w;3w;299w;3w;4w;100w;200w;10w;1w;3w;2w;4w;500w;1000w;12w;123w;93392039w;INT_MAXw])``
  |> concl |> rand |> listSyntax.dest_list |> fst |> map rand
  |> map stringSyntax.fromHOLstring |> concat |> print
*)

val _ = export_theory ();
