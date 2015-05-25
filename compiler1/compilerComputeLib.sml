structure compilerComputeLib = struct
local

open HolKernel boolLib bossLib computeLib
open modLangTheory source_to_modTheory

fun add_compiler_compset compset = let
  fun add_datatype t = compute_basicLib.add_datatype t compset
  (* modLang *)
  val () = add_datatype ``:modLang$exp``
  val () = add_datatype ``:modLang$dec``
  val () = add_datatype ``:modLang$prompt``
  (* source_to_mod *)
  val () = add_thms
    [source_to_modTheory.compile_prog_def
    ,source_to_modTheory.compile_top_def
    ,source_to_modTheory.compile_decs_def
    ,source_to_modTheory.compile_dec_def
    ,source_to_modTheory.compile_exp_def
    ,source_to_modTheory.alloc_defs_def
    ,source_to_modTheory.Bool_def
    ] compset
in () end

in

val add_compiler_compset = add_compiler_compset

val the_compiler_compset =
  let
    val c = compute_basicLib.the_basic_compset
    val () = compute_semanticsLib.add_ast_compset c
    val () = add_compiler_compset c
  in
    c
  end

end
