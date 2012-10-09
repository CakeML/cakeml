
open HolKernel Parse boolLib bossLib;

val _ = new_theory "bytecode_x64";

open BytecodeTheory x64_encodeLib wordsTheory wordsLib intLib;

(* define a mapping from list of bytecode instruction to 64-bit x86 *)

fun str2bytes str = let
  fun bytes (x1::x2::xs) =
    numSyntax.mk_numeral(Arbnum.fromHexString (implode [x1,x2])) :: bytes xs
    | bytes _ = []
  val xs = map (fn n => wordsSyntax.mk_n2w(n,``:8``)) (bytes (explode str))
  in listSyntax.mk_list(xs,``:word8``) end

val x86_bytes = str2bytes o x64_encode

val IMMEDIATE32_def = Define `
  IMMEDIATE32 (w:word32) =
    [w2w w; w2w (w >>> 8); w2w (w >>> 16); w2w (w >>> 24)]:word8 list`;

val bc2x64_aux_def = Define `
  (bc2x64_aux pos (Stack (PushInt i)) =
     if i < 0 then NONE else if 2**30 <= i then NONE else
       SOME [^(x86_bytes "push rax");
             TAKE 2 ^(x86_bytes "mov rax,20000") ++ IMMEDIATE32 (n2w (Num i * 2)) ++ IMMEDIATE32 0w]) /\
  (bc2x64_aux pos (Stack (Load n)) =
     if 2**28 <= n then NONE else
       SOME [^(x86_bytes "push rax");
             TAKE 4 ^(x86_bytes "mov rax,[rsp+20000]") ++ IMMEDIATE32 (n2w (8 * n))]) /\
  (bc2x64_aux pos (Stack (Store n)) =
     if 2**28 <= n then NONE else
       SOME [TAKE 4 ^(x86_bytes "mov [rsp+20000],rax") ++ IMMEDIATE32 (n2w (8 * n));
             ^(x86_bytes "pop rax")]) /\
  (bc2x64_aux pos (Stack (Pops n)) =
     if 2**28 <= n then NONE else
       SOME [TAKE 3 ^(x86_bytes "add rsp,20000") ++ IMMEDIATE32 (n2w (8 * n))]) /\
  (bc2x64_aux pos (Stack Pop) =
       SOME [^(x86_bytes "pop rax")]) /\
  (bc2x64_aux pos (Stack Add) =
       SOME [^(x86_bytes "pop rbx");
             ^(x86_bytes "add rax,rbx")]) /\
  (bc2x64_aux pos (Stack Sub) =
       SOME [^(x86_bytes "pop rbx");
             ^(x86_bytes "sub rbx,rax");
             ^(x86_bytes "mov rax,rbx")]) /\
  (bc2x64_aux pos (Stack Mult) =
       SOME [^(x86_bytes "pop rbx");
             ^(x86_bytes "shr rax,1");
             ^(x86_bytes "mul rbx")]) /\
  (bc2x64_aux pos (Stack Div) =
       SOME [^(x86_bytes "xor rbx,rbx");
             ^(x86_bytes "div rbx")]) /\
  (bc2x64_aux pos (Stack Mod) =
       SOME [^(x86_bytes "xor rbx,rbx");
             ^(x86_bytes "div rbx")]) /\
  (bc2x64_aux pos (Stack (Shift n k)) =
       if k = 0 then SOME [] else
       if n = 0 then
         if k = 1 then SOME [^(x86_bytes "pop rax")] else
           SOME [TAKE 3 ^(x86_bytes "add rsp,20000") ++ IMMEDIATE32 (n2w (8 * (k-1)));
                 ^(x86_bytes "pop rax")]
       else if n = 1 then
         SOME [TAKE 3 ^(x86_bytes "add rsp,20000") ++ IMMEDIATE32 (n2w (8 * k))]
       else if n = 2 then
         SOME [^(x86_bytes "pop rbx");
               TAKE 3 ^(x86_bytes "add rsp,20000") ++ IMMEDIATE32 (n2w (8 * k));
               ^(x86_bytes "push rbx")]
       else if n = 3 then
         SOME [^(x86_bytes "pop rbx");
               ^(x86_bytes "pop rcx");
               TAKE 3 ^(x86_bytes "add rsp,20000") ++ IMMEDIATE32 (n2w (8 * k));
               ^(x86_bytes "push rcx");
               ^(x86_bytes "push rbx")]
       else if n = 3 then
         SOME [^(x86_bytes "pop rbx");
               ^(x86_bytes "pop rcx");
               ^(x86_bytes "pop rdx");
               TAKE 3 ^(x86_bytes "add rsp,20000") ++ IMMEDIATE32 (n2w (8 * k));
               ^(x86_bytes "push rdx");
               ^(x86_bytes "push rcx");
               ^(x86_bytes "push rbx")]
       else
         SOME ((FLAT (GENLIST (\i.
                       [TAKE 4 ^(x86_bytes "mov rbx,[rsp+20000]") ++ IMMEDIATE32 (n2w (8 * (n-i-2)));
                        TAKE 4 ^(x86_bytes "mov [rsp+20000],rbx") ++ IMMEDIATE32 (n2w (8 * (k+n-i-2)))])
                          (n-1))) ++
               [TAKE 3 ^(x86_bytes "add rsp,20000") ++ IMMEDIATE32 (n2w (8 * k))])) /\
  (bc2x64_aux pos Return =
       SOME [^(x86_bytes "ret")]) /\
  (bc2x64_aux pos (Jump (Addr n)) =
       SOME [TAKE 2 ^(x86_bytes "jmp 20000") ++ IMMEDIATE32 (n2w n - 6w - n2w pos)]) /\
  (bc2x64_aux pos (Call (Addr n)) =
       SOME [TAKE 2 ^(x86_bytes "call 20000") ++ IMMEDIATE32 (n2w n - 6w - n2w pos)]) /\
  (bc2x64_aux pos JumpPtr =
       SOME [^(x86_bytes "mov rbx,rax");
             ^(x86_bytes "pop rax");
             ^(x86_bytes "jmp rbx")]) /\
  (bc2x64_aux pos CallPtr =
       SOME [^(x86_bytes "mov rbx,rax");
             ^(x86_bytes "pop rax");
             ^(x86_bytes "call rbx")]) /\
  (bc2x64_aux pos (JumpNil (Addr n)) =
       SOME [^(x86_bytes "test rax,rax");
             ^(x86_bytes "pop rax");
             TAKE 3 ^(x86_bytes "jne 20000") ++ IMMEDIATE32 (n2w n - 12w - n2w pos)]) /\
  (bc2x64_aux pos (Stack (Cons tag n)) =
       SOME ([^(x86_bytes "push rax");
              TAKE 2 ^(x86_bytes "mov rbx,20000") ++ IMMEDIATE32 (n2w n) ++ IMMEDIATE32 (n2w (2 * tag));
              ^(x86_bytes "mov [r15],rbx");
              ^(x86_bytes "lea rax,[r15+1]");
              TAKE 3 ^(x86_bytes "add r15,800000") ++ IMMEDIATE32 (n2w (8*(n+1)));
              ^(x86_bytes "mov rcx,r15")] ++
             (FLAT (GENLIST (\n.
                       [^(x86_bytes "pop rbx");
                        TAKE 3 ^(x86_bytes "mov [rcx+20000],rbx") ++
                          IMMEDIATE32 (0w - n2w (8*(n+1)))]) n)))) /\
  (bc2x64_aux pos Ref =
       SOME ([TAKE 2 ^(x86_bytes "mov rbx,20000") ++ IMMEDIATE32 (n2w 1) ++ IMMEDIATE32 (0w - 2w);
              ^(x86_bytes "mov [r15+8],rax");
              ^(x86_bytes "mov [r15],rbx");
              ^(x86_bytes "lea rax,[r15+1]");
              ^(x86_bytes "add r15,16")])) /\
  (bc2x64_aux pos (Stack (El n)) =
       SOME [TAKE 3 ^(x86_bytes "mov rax,[rax+80000]") ++ IMMEDIATE32 (n2w (8*(n+1)-1))]) /\
  (bc2x64_aux pos Deref =
       SOME [^(x86_bytes "mov rax,[rax+7]")]) /\
  (bc2x64_aux pos Update =
       SOME [^(x86_bytes "pop rbx");
             ^(x86_bytes "mov [rbx+7],rax");
             ^(x86_bytes "pop rax")]) /\
  (bc2x64_aux pos (Stack Less) =
       SOME [^(x86_bytes "pop rbx");
             ^(x86_bytes "cmp rax,rbx");
             ^(x86_bytes "mov rax,r8");
             ^(x86_bytes "cmova rax,r9")]) /\
  (bc2x64_aux pos (Stack IsNum) =
       SOME [^(x86_bytes "test rax,1");
             ^(x86_bytes "mov rax,r8");
             ^(x86_bytes "cmove rax,r9")]) /\
  (bc2x64_aux pos (Stack (TagEq n)) =
       SOME [^(x86_bytes "test rax,1");
             ^(x86_bytes "je 3");
             ^(x86_bytes "mov eax,[rax+3]");
             TAKE 2 ^(x86_bytes "cmp rax,200000") ++ IMMEDIATE32 (n2w (2 * n));
             ^(x86_bytes "mov rax,r8");
             ^(x86_bytes "cmove rax,r9")]) /\
  (bc2x64_aux pos (Stack Equal) =
       SOME [^(x86_bytes "mov rcx,rax");
             ^(x86_bytes "mov rax,2");
             ^(x86_bytes "pop rbx");
             ^(x86_bytes "cmp rbx,rcx");
             ^(x86_bytes "je 25"); (* the rest *)
             ^(x86_bytes "mov rdx,rbx");
             ^(x86_bytes "and rdx,rcx");
             ^(x86_bytes "test rdx,1");
             ^(x86_bytes "je 6"); (* next two *)
             ^(x86_bytes "xor rbx,rbx");
             ^(x86_bytes "div rbx"); (* intentionally div by zero *)
             ^(x86_bytes "xor rax,rax")]) /\
  (bc2x64_aux pos Exception =
       SOME [^(x86_bytes "xor rbx,rbx");
             ^(x86_bytes "div rbx")]) /\ (* intentionally div by zero *)
  (bc2x64_aux pos (Label _) = SOME []) /\
  (bc2x64_aux pos _ = NONE)`;

val bc_length_x64_def = Define `
  bc_length_x64 x =
    case bc2x64_aux 0 x of NONE => 0 | SOME bc => LENGTH (FLAT bc) - 1`;

val bytecode_to_x64_def = Define `
  bytecode_to_x64 bc =
    FST (FOLDL (\(res,pos) x. (SNOC (bc2x64_aux pos x) res,
                               pos + bc_length_x64 x + 1)) ([],0) bc)`;

val _ = export_theory();

