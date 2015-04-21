structure compute_x64Lib = struct local
open HolKernel boolLib bossLib computeLib
open bc_compileTheory
in
  val add_x64_compset = add_thms
   [inst_compile_def
   ,bc_compile_rev_eval
   ,bc_compile_rev_thm]

  fun the_x64_compset () =
    let
      val c = compute_basicLib.the_basic_compset
      val () = add_x64_compset c
    in c end
end
end
