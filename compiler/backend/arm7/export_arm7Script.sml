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
val startup_def = Define `
  startup ret pk =
    SmartAppend (List
      [strlit"\n";
       strlit"/* Start up code */\n";
       strlit"\n";
       strlit"     .text\n";
       strlit"     .p2align 3\n";
       strlit"     .globl  cdecl(cml_main)\n";
       strlit"     .globl  cdecl(cml_heap)\n";
       strlit"     .globl  cdecl(cml_stack)\n";
       strlit"     .globl  cdecl(cml_stackend)\n";
       strlit"     .type   cml_main, function\n";
       strlit"cdecl(cml_main):\n";
       strlit"     ldr    r0,=cake_main            /* arg1: entry address */\n";
       strlit"     ldr    r1,=cdecl(cml_heap)      /* arg2: first address of heap */\n";
       strlit"     ldr    r1,[r1]\n"])
    (SmartAppend (List
      (if ~pk then
        [strlit"     ldr    r2,=cake_bitmaps\n";
         strlit"     str    r2,[r1]                  /* store bitmap pointer */\n"]
      else []))
    (SmartAppend (List
      [strlit"     ldr    r2,=cdecl(cml_stack)     /* arg3: first address of stack */\n";
       strlit"     ldr    r2,[r2]\n";
       strlit"     ldr    r3,=cdecl(cml_stackend)  /* arg4: first address past the stack */\n";
       strlit"     ldr    r3,[r3]\n"])
    (SmartAppend (List
      (if ret then
        [strlit"     b      cml_enter\n"]
      else
        [strlit"     b      cake_main\n"]))
    (List
      [strlit"     .ltorg\n";
       strlit"\n"]))))`

val ffi_asm_def = Define `
  (ffi_asm [] = Nil) /\
  (ffi_asm (ffi::ffis) =
      SmartAppend (List [
       strlit"cake_ffi"; implode ffi; strlit":\n";
       strlit"     b     cdecl(ffi"; implode ffi; strlit")\n";
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
       "     b   cdecl(cml_exit)";
       "     .p2align 4";
       "";
       "cake_exit:"] ++
       (if ret then
         ["     b   cml_return"]
       else
         ["     b   cdecl(cml_exit)"]) ++
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

val entry_point_code =
  ``(List (MAP (\n. strlit(n ++ "\n"))
    [""; "";
     "cml_enter:";
     "     push   {r5,r6,r8,r10,r11,lr}";
     "     b      cake_main";
     "     .p2align 4";
     ""; "";
     "cml_return:";
     "     ldr    r5,=can_enter";
     "     mov    r6, #1";
     "     str    r6, [r5]";
     "     ldr    r5,=ret_base";
     "     str    r10, [r5]";
     "     ldr    r5,=ret_stack";
     "     str    r11, [r5]";
     "     ldr    r5,=ret_stackend";
     "     str    r8, [r5]";
     "     pop    {r5,r6,r8,r10,r11,lr}";
     "     bx     lr";
     "     .p2align 4";
     ""; "";
     "cake_enter:";
     "     push   {r5,r6,r8,r10,r11,lr}";
     "     ldr    r5,=can_enter";
     "     ldr    r6, [r5]";
     "     cmp    r6, #0";
     "     beq    cake_err3";
     "     mov    r6, #0";
     "     str    r6, [r5]";
     "     ldr    r5,=ret_base";
     "     ldr    r10, [r5]";
     "     ldr    r5,=ret_stack";
     "     ldr    r11, [r5]";
     "     ldr    r5,=ret_stackend";
     "     ldr    r8, [r5]";
     "     ldr    lr,=cake_return";
     "     bx     r4";
     "     .p2align 4";
     ""; "";
     "cake_return:";
     "     ldr    r5,=can_enter";
     "     mov    r6, #1";
     "     str    r6,  [r5]";
     "     pop    {r5,r6,r8,r10,r11,lr}";
     "     pop    {r4}";
     "     bx     lr";
     "     .p2align 4";
     ""; "";
     "cake_err3:";
     "     mov    r0, #3";
     "     b      cdecl(cml_err)";
     "     .p2align 4";
     ""]))`` |> EVAL |> concl |> rand;

val export_func_def = Define `
  export_func appl (name,label,start,len) =
    SmartAppend appl (List
    [strlit"\n     .globl  cdecl("; name; strlit")\n";
     strlit"     .type   "; name; strlit", function\n";
     strlit"cdecl("; name; strlit"):\n";
     strlit"     push   {r4}\n";
     strlit"     ldr    r4,="; name; strlit"_jmp\n";
     strlit"     b       cake_enter\n";
            name; strlit"_jmp:\n";
     strlit"     b       "; label; strlit"\n"
    ])`;

val export_funcs_def = Define `
  export_funcs lsyms exp =
    FOLDL export_func misc$Nil (FILTER ((flip MEM exp) o FST) lsyms)`;

val arm7_export_def = Define `
  arm7_export ffi_names bytes (data:word32 list) syms exp ret pk =
    let lsyms = get_sym_labels syms in
    SmartAppend
      (SmartAppend (List preamble)
      (SmartAppend (List (data_section ".long" ret))
      (SmartAppend (split16 (words_line (strlit"\t.long ") word_to_string) data)
      (SmartAppend (List data_buffer)
      (SmartAppend (startup ret pk) (^ffi_code ret))))))
      (SmartAppend (split16 (words_line (strlit"\t.byte ") byte_to_string) bytes)
      (SmartAppend (List code_buffer)
      (SmartAppend (emit_symbols lsyms)
      (if ret then
        (SmartAppend ^entry_point_code (export_funcs lsyms exp))
      else List []))))`;

val _ = export_theory ();
