open HolKernel bossLib repl_computeLib labels_computeLib replDecsTheory compileReplDecsTheory
val _ = new_theory"compileCallReplStepDec"

val _ = Globals.max_print_depth := 15

val bootstrap_lcode_def = new_definition("bootstrap_lcode_def",
  mk_eq(``bootstrap_lcode:bc_inst list``,
        rand(rand(rator(rand(rand(rand(rand(rhs(concl(repl_decs_compiled)))))))))))

val rev_bootstrap_lcode = save_thm("rev_bootstrap_lcode",
  (RAND_CONV(REWR_CONV bootstrap_lcode_def) THENC EVAL) ``REVERSE bootstrap_lcode``)

val internal_contab_def = new_definition("internal_contab_def",
  mk_eq(``internal_contab:contab``, rand(rator(rhs(concl(repl_decs_compiled))))))

val compile_repl_decs_internal =
  CONV_RULE(LAND_CONV(REWRITE_CONV[SYM compile_repl_decs_def]))
    (REWRITE_RULE[SYM bootstrap_lcode_def, SYM internal_contab_def]repl_decs_compiled)

val _ = computeLib.add_funs[call_repl_step_dec_def,compile_repl_decs_internal]

val call_repl_step_dec_compiled = save_thm("call_repl_step_dec_compiled",
  EVAL``
    let m = FST(SND(compile_repl_decs)) in
    let env = FST(SND(SND(compile_repl_decs))) in
    let rsz = FST(SND(SND(SND(compile_repl_decs)))) in
    let cs = SND(SND(SND(SND(compile_repl_decs)))) in
  compile_dec FEMPTY m env rsz <|out:=[];next_label:=cs.next_label|> call_repl_step_dec``);

val inst_length_def = Define`inst_length (i:bc_inst) = (0:num)` (* TODO: replace with real one *)

val code_labels_ok_rev_bootstrap_lcode =
  ASSUME ``code_labels_ok (REVERSE bootstrap_lcode)``
  |> CONV_RULE(RAND_CONV(REWR_CONV rev_bootstrap_lcode))

val code_labels_rev_bootstrap_lcode = save_thm("code_labels_rev_bootstrap_lcode",
  (RAND_CONV(REWR_CONV rev_bootstrap_lcode)
   THENC code_labels_conv code_labels_ok_rev_bootstrap_lcode (REWR_CONV inst_length_def))
    ``code_labels inst_length (REVERSE bootstrap_lcode)``)

val call_lcode_def = new_definition("call_lcode_def",
  mk_eq(``call_lcode:bc_inst list``,rand(rand(rator(rand(rhs(concl(call_repl_step_dec_compiled))))))))

val rev_call_lcode = save_thm("rev_call_lcode",
  (RAND_CONV(REWR_CONV call_lcode_def) THENC EVAL) ``REVERSE call_lcode``)

val code_labels_ok_rev_call_lcode =
  ASSUME ``code_labels_ok (REVERSE call_lcode)``
  |> CONV_RULE(RAND_CONV(REWR_CONV rev_call_lcode))

val code_labels_rev_call_lcode = save_thm("code_labels_rev_call_lcode",
  (RAND_CONV(REWR_CONV rev_call_lcode)
   THENC code_labels_conv code_labels_ok_rev_call_lcode (REWR_CONV inst_length_def))
    ``code_labels inst_length (REVERSE call_lcode)``)

val _ = export_theory()
