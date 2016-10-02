structure arm8_exportLib =
struct
local open HolKernel boolLib bossLib lcsymtacs in

fun cake_boilerplate_lines stack_mb heap_mb ffi_count = let
  val heap_line  = "    .space  " ^ (Int.toString heap_mb) ^
                   " * 1024 * 1024   # heap size in bytes"
  val stack_line = "    .space  " ^ Int.toString stack_mb ^
                   " * 1024 * 1024   # stack size in bytes"
  fun ffi_asm 0 = []
    | ffi_asm n = let
    val n = n - 1
    in ("cake_ffi" ^ (Int.toString n) ^ ":") ::
       "     pushq   %rax"::
       "     jmp     cdecl(ffi" ^ (Int.toString n) ^ ")"::
       "     .p2align 3"::
       "":: ffi_asm n end
  in
  ["#### Preprocessor to get around Mac OS and Linux differences in naming",
   "",
   "#if defined(__APPLE__)",
   "# define cdecl(s) _##s",
   "#else",
   "# define cdecl(s) s",
   "#endif",
   "",
   "     .file        \"cake.S\"",
   "",
   "#### Data section -- modify the numbers to change stack/heap size",
   "",
   "     .bss",
   "     .p2align 3",
   "cake_heap:",
   heap_line,
   "     .p2align 3",
   "cake_stack:",
   stack_line,
   "     .p2align 3",
   "cake_end:",
   "",
   "#### Start up code",
   "",
   "     .text",
   "     .globl  cdecl(main)",
   "cdecl(main):",
   "     pushq   %rbp        # push base pointer",
   "     movq    %rsp, %rbp  # save stack pointer",
   "     leaq    cake_main(%rip), %rdi   # arg1: entry address",
   "     leaq    cake_heap(%rip), %rsi   # arg2: first address of heap",
   "     leaq    cake_stack(%rip), %rbx  # arg3: first address of stack",
   "     leaq    cake_end(%rip), %rdx    # arg4: first address past the stack",
   "     jmp     cake_main",
   "",
   "#### CakeML FFI interface (each block is 8 bytes long)",
   "",
   "     .p2align 3",
   ""] @
   ffi_asm ffi_count @
  ["cake_clear:",
   "     callq   cdecl(exit)",
   "     .p2align 3",
   "",
   "cake_exit:",
   "     callq   cdecl(exit)",
   "     .p2align 3",
   "",
   "cake_main:",
   "",
   "#### Output of the CakeML compiler follows",
   ""]
  end |> map (fn s => s ^ "\n");

fun byte_list_to_asm_lines bytes = let
  val (xs,ty) = listSyntax.dest_list bytes
  val _ = (ty = ``:word8``) orelse failwith "not a list of bytes"
  fun fill c d n s = if size s < n then fill c d n (c ^ s ^ d) else s
  fun word2hex tm = let
    val s = wordsSyntax.dest_n2w tm |> fst
              |> numSyntax.dest_numeral |> Arbnum.toHexString
    in "0x" ^ fill "0" "" 2 s end
  fun commas [] = ""
    | commas [x] = x
    | commas (x::xs) = x ^ "," ^ commas xs
  fun take_drop n [] = ([],[])
    | take_drop n xs =
        if n = 0 then ([],xs) else let
          val (ys,zs) = take_drop (n-1) (tl xs)
          in (hd xs :: ys, zs) end
  val bytes_per_line = 12
  fun bytes_to_strings [] = []
    | bytes_to_strings xs = let
        val (ys,zs) = take_drop bytes_per_line xs
        in "  .byte " ^ commas (map word2hex ys) ^ "\n" ::
           bytes_to_strings zs end
  in bytes_to_strings xs end;

fun cake_lines stack_mb heap_mb ffi_count bytes_tm =
  cake_boilerplate_lines stack_mb heap_mb ffi_count @
  byte_list_to_asm_lines bytes_tm;

fun write_cake_S stack_mb heap_mb ffi_count bytes_tm filename = let
  val lines = cake_lines stack_mb heap_mb ffi_count bytes_tm
  val f = TextIO.openOut filename
  fun each g [] = ()
    | each g (x::xs) = (g x; each g xs)
  val _ = each (fn line => TextIO.output (f,line)) lines
  val _ = TextIO.closeOut f
  val _ = print ("Generated " ^ filename ^ " (" ^ Int.toString (length lines) ^ " lines)\n")
  in () end

(*

val _ = write_cake_S 50 50 0 bytes_tm ""

*)
end
end
