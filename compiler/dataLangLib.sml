(*
  Library for in-logic compilation of CakeML abstract syntax into
  dataLang abstract syntac using the CakeML compiler backend.
*)

structure dataLangLib = structure

open preamble basis compilationLib;

fun to_data backend_config_def prog name =
  let
    val heap_size      = 1000
    val stack_size     = 1000
    val prog_def       = REFL (process_topdecs prog)
    val cs             = compilation_compset()
    val conf_def       = backend_config_def
    val data_prog_name = name ^ "_data_prog"
    val to_data_thm    = compile_to_data cs conf_def prog_def data_prog_name
    val data_prog_def  = definition(mk_abbrev_name data_prog_name)
    val bvi_conf_def   = definition (mk_abbrev_name "bvi_conf")
    (* configuration *)
    val conf      =  ``^(rhs (concl bvi_conf_def))``
    val conf_name = mk_var (name ^ "_data_conf", type_of conf)
    val conf_def  = Define `^conf_name = ^conf`
    (* code *)
    val code      = ``fromAList ^(rhs (concl data_prog_def))``
    val code_name = mk_var (name ^ "_data_code", type_of code)
    val code_def  = Define `^code_name = ^code`
    (* initial call *)
    val initial_call = ``dataLang$Call NONE (SOME ^(conf).clos_conf.start)
                                       [] NONE``
    val initial_call_name = mk_var (name ^ "_data_call", type_of initial_call)
    val initial_call_def  = Define `^initial_call_name = ^initial_call`
  in
    (initial_call,code,conf)
  end

val to_data_arm7  = to_data arm7_backend_config_def
val to_data_arm8  = to_data arm8_backend_config_def
val to_data_mips  = to_data mips_backend_config_def
val to_data_riscv = to_data riscv_backend_config_def
val to_data_ag32  = to_data ag32_backend_config_def
val to_data_x64   = to_data x64_backend_config_def

end
