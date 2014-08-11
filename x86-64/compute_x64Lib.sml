structure compute_x64Lib = struct local
open HolKernel boolLib bossLib computeLib
open x64_code_evalTheory x64_heapTheory
in
  val add_x64_compset = add_thms
   [prog_x64_extraTheory.IMM32_def
   ,small_offset_def
   ,small_offset6_def
   ,small_offset12_def
   ,small_offset16_def
   ,x64_def
   ,x64_length_def
   ,x64_code_def]

  fun the_x64_compset () =
    let
      val c = compute_basicLib.the_basic_compset
      val () = add_x64_compset c
    in c end
end
end
