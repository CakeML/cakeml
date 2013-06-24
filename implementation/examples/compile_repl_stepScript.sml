open preamble repl_computeLib ml_repl_stepTheory
val _ = new_theory"compile_repl_step"

val _ = Hol_datatype`stop_list = stop_NIL | stop_CONS of 'a => stop_list`

val _ = computeLib.stoppers := let
  val stop_CONS = inst[alpha|->``:bc_inst list``]``stop_CONS``
  val stoppers = [stop_CONS ,``Dlet``,``Dletrec``,``Dtype``]
  in SOME (fn tm => mem tm stoppers) end

val compile_decs = Define`
  compile_decs cs [] acc = acc ∧
  compile_decs cs (d::ds) acc =
  let (css,csf,code) = compile_top cs (Tdec d) in
  compile_decs css ds (stop_CONS code acc)`

val _ = computeLib.add_funs[ml_repl_step_decls]

(*
val _ = Globals.max_print_depth := 20

val _ = PolyML.fullGC();
val res = time EVAL
  ``compile_decs init_compiler_state (TAKE 100 ml_repl_step_decls) stop_NIL``
*)

(*
EVAL ``TAKE 20 (DROP 100 ml_repl_step_decls)``
val _ = time EVAL ``compile_decs init_compiler_state ml_repl_step_decls stop_NIL``
*)

(*
val Dlet_o = time EVAL ``EL 11 ml_repl_step_decls`` |> concl |> rhs
val many_o10 = EVAL ``GENLIST (K ^Dlet_o) 10`` |> concl |> rhs
val many_o20 = EVAL ``GENLIST (K ^Dlet_o) 20`` |> concl |> rhs
val many_o40 = EVAL ``GENLIST (K ^Dlet_o) 40`` |> concl |> rhs
val many_o80 = EVAL ``GENLIST (K ^Dlet_o) 80`` |> concl |> rhs

val _ = PolyML.fullGC();
val _ = time EVAL ``compile_decs init_compiler_state ^many_o10 stop_NIL``
val _ = PolyML.fullGC();
val _ = time EVAL ``compile_decs init_compiler_state ^many_o20 stop_NIL``
val _ = PolyML.fullGC();
val _ = time EVAL ``compile_decs init_compiler_state ^many_o40 stop_NIL``
val _ = PolyML.fullGC();
val _ = time EVAL ``compile_decs init_compiler_state ^many_o80 stop_NIL``

val _ = computeLib.stoppers := NONE
val num_compset = reduceLib.num_compset()
*)

val _ = export_theory()
