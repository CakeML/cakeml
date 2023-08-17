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
val startup =
  ``(MAP (\n. strlit(n ++ "\n"))
      ["/* Start up code */";
       "";
       "     .text";
       "     .p2align 12";
       "     .globl  cdecl(cake_text_begin)";
       "cdecl(cake_text_begin):";
       "     .globl  cdecl(cml_main)";
       "     .globl  cdecl(cml_heap)";
       "     .globl  cdecl(cml_stack)";
       "     .globl  cdecl(cml_stackend)";
       "#ifndef __APPLE__";
       "     .type   cml_main, function";
       "#endif";
       "cdecl(cml_main):";
       "     pushq   %rbp                            # push base pointer";
       "     movq    %rsp, %rbp                      # save stack pointer";
       "     leaq    cake_main(%rip), %rdi           # arg1: entry address";
       "     movq    cdecl(cml_heap)(%rip), %rsi     # arg2: first address of heap";
       "     leaq    cake_bitmaps(%rip), %rax";
       "     movq    %rax, 0(%rsi)                   # store bitmap pointer";
       "     leaq    cdecl(cake_bitmaps_buffer_begin)(%rip), %rax";
       "     movq    %rax, 8(%rsi)                   # store bitmap mutable start pointer";
       "     leaq    cdecl(cake_bitmaps_buffer_end)(%rip), %rax";
       "     movq    %rax, 16(%rsi)                  # store bitmap mutable end pointer";
       "     leaq    cdecl(cake_codebuffer_begin)(%rip), %rax";
       "     movq    %rax, 24(%rsi)                  # store code mutable start pointer";
       "     leaq    cdecl(cake_codebuffer_end)(%rip), %rax";
       "     movq    %rax, 32(%rsi)                  # store code mutable end pointer";
       "     movq    cdecl(cml_stack)(%rip), %rdx    # arg3: first address of stack";
       "     movq    cdecl(cml_stackend)(%rip), %rcx # arg4: first address past the stack";
       "     jmp     cake_main";
       ""])`` |> EVAL |> concl |> rand

val ffi_asm_def = Define `
  (ffi_asm [] = Nil) /\
  (ffi_asm (ffi::ffis) =
      SmartAppend (List [
       strlit"cake_ffi"; implode ffi; strlit":\n";
       strlit"     pushq   %rax\n";
       strlit"     jmp     wcdecl(ffi"; implode ffi; strlit")\n";
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
       "     pushq   %rax";
       "     pushq   %rdi";
       "     callq   wcdecl(cml_clear)";
       "     popq    %rdi";
       "     ret";
       "     .p2align 4";
       "";
       "cake_exit:";
       "     callq   wcdecl(cml_exit)";
       "     .p2align 4";
       "";
       "cake_main:";
       "";
       "/* Generated machine code follows */";
       ""])))`` |> EVAL |> concl |> rand

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

val windows_ffi_code =
  ``SmartAppend
    (
     List [strlit "\n/* Windows Compatibility for CakeML FFI interface */\n\n"]
    )
    (
    SmartAppend
     (windows_ffi_asm (REVERSE ffi_names))
     (List (MAP (\n. strlit(n ++ "\n"))
      ["windows_cml_exit:";
       "     movq    %rcx, %r9";
       "     movq    %rdx, %r8";
       "     movq    %rsi, %rdx";
       "     movq    %rdi, %rcx";
       "     callq   cdecl(cml_exit)";
       ""])))`` |> EVAL |> concl |> rand

val x64_export_def = Define `
  x64_export ffi_names bytes (data:word64 list) syms =
    SmartAppend
      (SmartAppend
      (SmartAppend (List preamble)
      (SmartAppend (List (data_section ".quad"))
      (SmartAppend (split16 (words_line (strlit"\t.quad ") word_to_string) data)
      (SmartAppend (List data_buffer)
      (SmartAppend (List ((strlit"\n")::^startup)) ^ffi_code)))))
      (SmartAppend (split16 (words_line (strlit"\t.byte ") byte_to_string) bytes)
      (SmartAppend (List code_buffer)
      (emit_symbols syms))))
      (^windows_ffi_code)`;

(*
  EVAL``append(split16 (words_line (strlit"\t.quad ") word_to_string) [100w:word64;393w;392w])``

  EVAL ``append (x64_export ["getArgs";"putChar";"getChar"] 400 300
    [3w;4w;5w;9w;11w;12w;13w;14w;79w;12w;91w;21w;34w;32w;53w;255w;128w;122w;127w]
    [0w;3w;2w;9w;3w;299w;3w;4w;100w;200w;10w;1w;3w;2w;4w;500w;1000w;12w;123w;93392039w;INT_MAXw])``
  |> concl |> rand |> listSyntax.dest_list |> fst |> map rand
  |> map stringSyntax.fromHOLstring |> concat |> print
*)

val _ = export_theory ();
