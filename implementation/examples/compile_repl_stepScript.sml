open preamble repl_computeLib ml_repl_stepTheory
val _ = new_theory"compile_repl_step"

val _ = Hol_datatype`stop_list = stop_NIL | stop_CONS of 'a => stop_list`

val _ = computeLib.stoppers := let
  val stop_CONS = inst[alpha|->``:bc_inst list``]``stop_CONS``
  val stoppers = [stop_CONS ,``Dlet``,``Dletrec``,``Dtype``]
  in SOME (fn tm => mem tm stoppers) end

val _ = let
  open computeLib (* TODO: these calls should be automatic in HOL *)
  (*
  EVAL ``MAP (λdec. case dec of Dtype ts => MAP (FST o SND) ts) (FILTER (λdec. case dec of Dtype _ => T | _ => F) ml_repl_step_decls)``
  *)
in
  set_skip the_compset ``evalcase_CASE`` (SOME 1);
  set_skip the_compset ``list_CASE`` (SOME 1);
  set_skip the_compset ``option_CASE`` (SOME 1);
  set_skip the_compset ``sum_CASE`` (SOME 1);
  set_skip the_compset ``id_CASE`` (SOME 1);
  set_skip the_compset ``tc0_CASE`` (SOME 1);
  set_skip the_compset ``t_CASE`` (SOME 1);
  set_skip the_compset ``lit_CASE`` (SOME 1);
  set_skip the_compset ``pat_CASE`` (SOME 1);
  set_skip the_compset ``lop_CASE`` (SOME 1);
  set_skip the_compset ``opb_CASE`` (SOME 1);
  set_skip the_compset ``opn_CASE`` (SOME 1);
  set_skip the_compset ``op_CASE`` (SOME 1);
  set_skip the_compset ``uop_CASE`` (SOME 1);
  set_skip the_compset ``error_CASE`` (SOME 1);
  set_skip the_compset ``exp_CASE`` (SOME 1);
  set_skip the_compset ``dec_CASE`` (SOME 1);
  set_skip the_compset ``spec_CASE`` (SOME 1);
  set_skip the_compset ``top_CASE`` (SOME 1);
  set_skip the_compset ``ast_t_CASE`` (SOME 1);
  set_skip the_compset ``ast_pat_CASE`` (SOME 1);
  set_skip the_compset ``ast_exp_CASE`` (SOME 1);
  set_skip the_compset ``ast_dec_CASE`` (SOME 1);
  set_skip the_compset ``ast_spec_CASE`` (SOME 1);
  set_skip the_compset ``ast_top_CASE`` (SOME 1);
  set_skip the_compset ``bc_stack_op_CASE`` (SOME 1);
  set_skip the_compset ``bc_inst_CASE`` (SOME 1);
  set_skip the_compset ``compiler_state_CASE`` (SOME 1);
  set_skip the_compset ``Cpat_CASE`` (SOME 1);
  set_skip the_compset ``exp_to_Cexp_state_CASE`` (SOME 1);
  set_skip the_compset ``compiler_result_CASE`` (SOME 1);
  set_skip the_compset ``call_context_CASE`` (SOME 1);
  set_skip the_compset ``ctbind_CASE`` (SOME 1);
  set_skip the_compset ``COND`` (SOME 1);
end

val compile_decs = Define`
  compile_decs cs [] acc = acc ∧
  compile_decs cs (d::ds) acc =
  let (cs,code) = compile_dec cs d in
  compile_decs cs ds (stop_CONS code acc)`

val _ = computeLib.add_funs[ml_repl_step_decls]

val _ = Globals.max_print_depth := 20

(*
val _ = PolyML.fullGC();

EVAL ``TAKE 20 (DROP 100 ml_repl_step_decls)``
val res = time EVAL ``compile_decs init_compiler_state (TAKE 120 ml_repl_step_decls) stop_NIL``
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
