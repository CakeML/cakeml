structure x64_exportLib =
struct
local open HolKernel boolLib bossLib lcsymtacs in

fun commas [] = ""
  | commas [x] = x
  | commas (x::xs) = x ^ "," ^ commas xs
fun take_drop n [] = ([],[])
  | take_drop n xs =
      if n = 0 then ([],xs) else let
        val (ys,zs) = take_drop (n-1) (tl xs)
        in (hd xs :: ys, zs) end

  fun bytes_to_strings [] = []
    | bytes_to_strings xs = let
        val (ys,zs) = take_drop bytes_per_line xs
        in "     .byte " ^ commas (map word2hex ys) ^ "\n" ::
           bytes_to_strings zs end

fun cake_boilerplate_lines stack_mb heap_mb ffi_names data_words = let
  val heap_line  = "     .space  " ^ (Int.toString heap_mb) ^
                   " * 1024 * 1024   # heap size in bytes"
  val stack_line = "     .space  " ^ Int.toString stack_mb ^
                   " * 1024 * 1024   # stack size in bytes"
  fun ffi_asm [] = []
    | ffi_asm (ffi::ffis) =
      ("cake_ffi" ^ ffi ^ ":") ::
       "     pushq   %rax"::
       "     jmp     cdecl(ffi" ^ ffi ^ ")"::
       "     .p2align 4"::
       "":: ffi_asm ffis
  val bitmaps_per_line = 12
  fun bitmaps_asm [] = []
    | bitmaps_asm ws = let
      val (ys,zs) = take_drop bitmaps_per_line ws
      in "     .quad " ^ commas (map (Word64.fmt StringCvt.DEC) ys)
      :: bitmaps_asm zs end
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
   "     .data",
   "     .p2align 3",
   "cdecl(argc): .quad 0",
   "cdecl(argv): .quad 0",
   "cake_bitmaps:"] @
     bitmaps_asm data_words @ [
   "",
   "#### Start up code",
   "",
   "     .text",
   "     .p2align 3",
   "     .globl  cdecl(main)",
   "     .globl  cdecl(argc)",
   "     .globl  cdecl(argv)",
   "cdecl(main):",
   "     leaq    cdecl(argc)(%rip), %rbx",
   "     leaq    cdecl(argv)(%rip), %rdx",
   "     movq    %rdi, 0(%rbx)  # %rdi stores argc",
   "     movq    %rsi, 0(%rdx)  # %rsi stores argv",
   "     pushq   %rbp        # push base pointer",
   "     movq    %rsp, %rbp  # save stack pointer",
   "     leaq    cake_main(%rip), %rdi   # arg1: entry address",
   "     leaq    cake_heap(%rip), %rsi   # arg2: first address of heap",
   "     leaq    cake_bitmaps(%rip), %rbx",
   "     movq    %rbx, 0(%rsi)           # store bitmap pointer",
   "     leaq    cake_stack(%rip), %rbx  # arg3: first address of stack",
   "     leaq    cake_end(%rip), %rdx    # arg4: first address past the stack",
   "     jmp     cake_main",
   "",
   "#### CakeML FFI interface (each block is 16 bytes long)",
   "",
   "     .p2align 3",
   ""] @
   ffi_asm ffi_names @
  ["cake_clear:",
   "     callq   cdecl(exit)",
   "     .p2align 4",
   "",
   "cake_exit:",
   "     callq   cdecl(exit)",
   "     .p2align 4",
   "",
   "cake_main:",
   "",
   "#### Output of the CakeML compiler follows",
   ""]
  end |> map (fn s => s ^ "\n");

fun byte_list_to_asm_lines bytes = let
  fun fill c d n s = if size s < n then fill c d n (c ^ s ^ d) else s
  fun word2hex w =
    let val s = Word8.fmt StringCvt.HEX w
    in "0x" ^ fill "0" "" 2 s end
  val bytes_per_line = 12
  fun bytes_to_strings [] = []
    | bytes_to_strings xs = let
        val (ys,zs) = take_drop bytes_per_line xs
        in "     .byte " ^ commas (map word2hex ys) ^ "\n" ::
           bytes_to_strings zs end
  in bytes_to_strings bytes end;

fun cake_lines stack_mb heap_mb ffi_names data_words code_words =
  cake_boilerplate_lines stack_mb heap_mb ffi_names data_words @
  byte_list_to_asm_lines code_words;

fun write_cake_S stack_mb heap_mb ffi_names data_words code_words filename = let
  val lines = cake_lines stack_mb heap_mb (List.rev ffi_names) data_words code_words
  val f = TextIO.openOut filename
  fun each g [] = ()
    | each g (x::xs) = (g x; each g xs)
  val _ = each (fn line => TextIO.output (f,line)) lines
  val _ = TextIO.closeOut f
  val _ = print ("Generated " ^ filename ^ " (" ^ Int.toString (length lines) ^ " lines)\n")
  in () end

(*

val _ = write_cake_S 50 50 [] ``[3w:word8;3w:word8;3w:word8;3w:word8;3w:word8;3w:word8;3w:word8;3w:word8;3w:word8;3w:word8;3w:word8;3w:word8;3w:word8;3w:word8;3w:word8;3w:word8;3w:word8;3w:word8;3w:word8;3w:word8;3w:word8;3w:word8;3w:word8;3w:word8;3w:word8;3w:word8]`` "t"

*)
end
end
